"""Pure Python/git recovery tests. Build oracle is injected; no Lean command runs."""
import json, math, os, pathlib, subprocess, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import batch_recovery as br
import pipeline_guard as guard
import stage3_delivery as s3
os.environ["SHEAF_LEAD"] = "L-only"
import batch_land as bl
import add_proof_imports as api


class Repo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.g('init', '-q'); self.g('config', 'user.email', 'test@example.invalid'); self.g('config', 'user.name', 'test')
        for m in 'ABC': self.put(f'lean/Sheaf/{m}.lean', f'module\n\npublic theorem {m} : True := by sorry\n')
        self.put('coord/ledger.md', 'base ledger\n'); self.put('coord/deliveries.log', 'base log\n')
        self.put('dag/nodes/x/a.json', json.dumps({'id': 'a', 'lean': {'module': 'Sheaf.A'}, 'lean_audit': {'sheaf-dag': {'state': 'sorry'}}, 'proved': False}))
        self.put(".gitignore", "local/\nalerts/\n")
        self.base = self.commit('published green')
        self.put('lean/Sheaf/A.lean', 'module\n\npublic theorem A : True := by trivial\n')
        self.put('dag/nodes/x/a.json', json.dumps({'id': 'a', 'lean': {'module': 'Sheaf.A'}, 'lean_audit': {'sheaf-dag': {'state': 'closed'}}, 'proved': True}))
        self.put('coord/ledger.md', 'base ledger\nlanding line\n'); self.put('coord/deliveries.log', 'base log\nlanding line\n')
        self.landed = self.commit('land delivery')
    def g(self, *args): return br.git(self.root, *args).decode().strip()
    def put(self, path, data):
        p = self.root / path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(data)
    def commit(self, msg): self.g('add', '.'); self.g('commit', '-qm', msg); return self.g('rev-parse', 'HEAD')
    def install(self, prepared): br.commit_inverse(self.root, prepared, self.g('rev-parse', 'HEAD'), 'take-out test')
    def test_later_import_only(self):
        text = (self.root / 'lean/Sheaf/A.lean').read_text()
        self.put('lean/Sheaf/A.lean', text.replace('module\n', 'module\nimport Sheaf.B\nimport Sheaf.DoesNotExist\n'))
        self.commit('proof imports')
        self.install(br.inverse(self.root, [self.landed], imports_only=True))
        self.assertEqual((self.root / 'lean/Sheaf/A.lean').read_text(), 'module\nimport Sheaf.B\n\npublic theorem A : True := by sorry\n')
    def test_real_change_falls_to_withdrawal(self):
        p = self.root / 'lean/Sheaf/A.lean'; p.write_text(p.read_text() + '\n-- maintainer\n')
        self.commit('maintainer')
        with self.assertRaises(br.Conflict): br.inverse(self.root, [self.landed], imports_only=True)
        self.install(br.inverse(self.root, [self.landed]))
        self.assertIn('-- maintainer', p.read_text()); self.assertIn('sorry', p.read_text())
    def test_withdrawal_keeps_maintainer_commit(self):
        self.put('lean/Sheaf/C.lean', 'module\n-- independent maintainer change\n')
        self.put('coord/ledger.md', 'base ledger\nlanding line\nmaintainer line\n')
        maint = self.commit('maintainer between batch and withdrawal')
        self.install(br.inverse(self.root, [self.landed]))
        self.assertEqual(self.g('merge-base', maint, 'HEAD'), maint)
        self.assertIn('maintainer change', (self.root / 'lean/Sheaf/C.lean').read_text())
        self.assertEqual((self.root / 'coord/ledger.md').read_text(), 'base ledger\nmaintainer line\n')
        self.assertFalse(json.loads((self.root / 'dag/nodes/x/a.json').read_text())['proved'])
    def test_created_node_backfill_and_renewed_claim(self):
        self.put('dag/nodes/x/new.json', json.dumps({'id': 'new', 'statement': 'true', 'blueprint': {'from': 'delivery'}}))
        self.put('coord/claims/item.lock', '{"who":"G", "t":1}')
        self.commit('claim before delivery')
        (self.root / 'coord/claims/item.lock').unlink()
        sha = self.commit('delivery removes claim')
        self.put('coord/claims/item.lock', '{"who":"G", "t":2}')
        self.commit('worker renews claim')
        self.install(br.inverse(self.root, [sha]))
        self.assertEqual(json.loads((self.root / 'coord/claims/item.lock').read_text())['t'], 2)
        self.assertIsNone(br.merge_json(None, b'{"id":"new","statement":"true","blueprint":{"from":"delivery"}}',
                                      b'{"id":"new","statement":"true","blueprint":{"from":"backfill"}}'))

    def test_record_consistency_with_fake_probe(self):
        import landing as ld
        local = self.root / 'local'; builds = local / 'builds'
        for d in ('requests', 'done', 'backup'): (builds / d).mkdir(parents=True)
        rec = {'id': 'L', 'group': 'G', 'files': [{'path': 'Sheaf/A.lean', 'module': 'Sheaf.A'}], 'sorry_allowed': {'Sheaf.A': []}}
        (builds / 'requests/L.json').write_text(json.dumps(rec))
        e = {'commit': self.landed, 'landing': 'L', 'group': 'G', 'item': 'Sheaf.A', 'claim': '{"who":"G"}', 'head': self.landed}
        with patch.object(bl, 'ROOT', self.root), patch.object(bl.md, 'ROOT', self.root), patch.object(ld.li, 'LEAN', self.root / 'lean'), \
             patch.object(ld, 'LOCAL', local), patch.object(ld, 'REQUESTS', builds / 'requests'), patch.object(ld, 'DONE', builds / 'done'), \
             patch.object(bl.md, 'merge_lock', lambda: __import__('contextlib').nullcontext()), patch.object(bl, 'refresh_recovery_queue'):
            bl.undo_entries([e], 'compiler error and triage breaker', returned=True)
        done = json.loads((builds / 'done/L.json').read_text())
        # Fake build probe uses the same allowed-name comparison as build.batch_checks.
        found = {k for k, d in s3.decl_table((self.root / 'lean/Sheaf/A.lean').read_text()).items() if d['sorry']}
        self.assertEqual(found, set(done['sorry_allowed']['Sheaf.A']))
        self.assertFalse((builds / 'requests/L.json').exists())
        self.assertEqual(json.loads((self.root / 'coord/claims/Sheaf.A.lock').read_text())['who'], 'G')
        self.assertIn('triage breaker', (self.root / 'coord/returns/G.md').read_text())
    def test_live_bisection_state_machine_with_injected_build(self):
        import copy, contextlib, landing as ld
        local = self.root / 'local'; builds = local / 'builds'
        for d in ('requests', 'done', 'backup'): (builds / d).mkdir(parents=True)
        entries = []
        for i in range(8):
            p = self.root / 'lean/Sheaf/A.lean'; p.write_text(p.read_text() + f'-- delivery {i}\n')
            sha = self.commit(f'delivery {i}')
            entries.append({'group': 'G', 'item': f'Sheaf.Item{i}', 'head': sha, 'commit': sha,
                            'landing': f'L{i}', 'state': 'landed', 'modules': ['Sheaf.A'], 'reviewer': 'test'})
        logs, calls = [], []
        b = {'id': 'batch', 'entries': copy.deepcopy(entries), 'round': 1}
        def put_result(ids, result):
            calls.append(ids)
            ld.write_json(builds / 'last.json', {'time': str(len(calls)), 'result': result, 'included': ids,
                          'verified': ids if result == 'green' else [], 'failing': ['Sheaf.A'], 'errors': ['bad delivery 0']})
        def land_subset(b, chosen):
            out = []
            for e in chosen:
                p = self.root / 'lean/Sheaf/A.lean'
                i = e['item'].removeprefix('Sheaf.Item'); p.write_text(p.read_text() + f'-- delivery {i}\n')
                sha = self.commit('reland ' + i)
                x = dict(e, commit=sha, landing='new' + sha, state='landed')
                ld.write_json(builds / ('requests/' + x['landing'] + '.json'),
                              {'id': x['landing'], 'group': 'G', 'files': [{'path': 'Sheaf/A.lean', 'module': 'Sheaf.A'}]})
                out.append(x)
            return out
        with patch.object(bl, 'ROOT', self.root), patch.object(bl.md, 'ROOT', self.root), \
             patch.object(bl, 'OPEN', local / 'batch/open.json'), patch.object(bl, 'CLOSED', local / 'batch/closed'), \
             patch.object(bl, 'PASSED', local / 'batch/passed'), patch.object(ld.li, 'LEAN', self.root / 'lean'), \
             patch.object(ld, 'LOCAL', local), patch.object(ld, 'B', builds), patch.object(ld, 'REQUESTS', builds / 'requests'), \
             patch.object(ld, 'DONE', builds / 'done'), patch.object(bl.md, 'merge_lock', lambda: contextlib.nullcontext()), \
             patch.object(bl, 'refresh_recovery_queue'), patch.object(bl, 'reland_subset', land_subset), \
             patch.dict(os.environ, {'SHEAF_ALERT_DIR': str(self.root / 'alerts')}):
            ld.write_json(builds / 'last.json', {'time': '0', 'result': 'red', 'failing': ['Sheaf.A']})
            bl.withdraw(b, 'failed take-out', lambda *x: logs.append(x))
            for _ in range(8):
                r = b['recovery']; ids = [e['landing'] for e in r.get('tested', [])]
                text = (self.root / 'lean/Sheaf/A.lean').read_text()
                put_result(ids, 'red' if '-- delivery 0\n' in text else 'green')
                bl.recovery_step(b, lambda *x: logs.append(x))
                if not (local / 'batch/open.json').exists(): break
            else: self.fail('recovery did not close')
        self.assertEqual(len(calls), 5)
        self.assertEqual(sum(e['state'] == 'verified' for e in b['entries']), 7)
        self.assertEqual(b['entries'][0]['state'], 'returned')
        self.assertNotIn('-- delivery 0\n', (self.root / 'lean/Sheaf/A.lean').read_text())

    def test_transaction_conflict_writes_nothing(self):
        p = self.root / 'lean/Sheaf/A.lean'; p.write_text(p.read_text().replace('trivial', 'other'))
        self.commit('overlapping maintainer edit'); before = p.read_bytes()
        with self.assertRaises(br.Conflict): br.inverse(self.root, [self.landed])
        self.assertEqual(p.read_bytes(), before)
    def test_alert_lifecycle(self):
        guard.alert('batch', 'Sheaf.A', 'revert failed', 'withdraw', self.root)
        first = (self.root / 'ALERT').read_text(); guard.alert('batch', 'Sheaf.B', 'retry', 'repair', self.root)
        self.assertEqual((self.root / 'ALERT').read_text(), first)
        guard.clear_alert(self.root); self.assertFalse((self.root / 'ALERT').exists())
        self.assertEqual((self.root / 'ALERT.log').read_text(), first)
    def test_import_guard_refuses_open_batch_and_pending_file(self):
        self.put('local/batch/open.json', '{}')
        with self.assertRaises(RuntimeError): guard.proof_imports_guard(self.root)
        (self.root / 'local/batch/open.json').unlink()
        self.put('local/builds/requests/L.json', json.dumps({'id': 'L', 'files': [{'module': 'Sheaf.A'}]}))
        with self.assertRaises(RuntimeError): guard.proof_imports_guard(self.root, ['Sheaf.A'])
        guard.proof_imports_guard(self.root, ['Sheaf.B'])
        with patch.object(api.li, 'ROOT', self.root):
            with self.assertRaises(RuntimeError): api.write([('Sheaf.A', 'Sheaf.B', [], '')], False)
    def test_source_fingerprint_ignores_ledger_but_detects_source(self):
        a = guard.source_fingerprint(self.root / 'lean')
        self.put('coord/ledger.md', 'later'); self.assertEqual(a, guard.source_fingerprint(self.root / 'lean'))
        self.put('lean/Sheaf/C.lean', 'changed'); self.assertNotEqual(a, guard.source_fingerprint(self.root / 'lean'))


class Logic(unittest.TestCase):
    def test_eight_deliveries_one_bad_injected_build(self):
        seen = []
        def fake_build(group): seen.append(list(group)); return 0 not in group
        good, bad, builds = br.replay_bisect(list(range(8)), fake_build)
        self.assertEqual(bad, [0]); self.assertEqual(set(good), set(range(1, 8)))
        self.assertEqual(builds, 5); self.assertEqual(len(seen), 5)
    def test_bisection_every_position(self):
        for bad in range(8):
            good, found, builds = br.replay_bisect(list(range(8)), lambda group: bad not in group)
            self.assertEqual(found, [bad]); self.assertEqual(builds, math.ceil(math.log2(8)) + 2)
    def test_reader_rules(self):
        old = 'module\npublic import Sheaf.B\npublic theorem a : True := by sorry\n'
        for addition in ('instance myInst : X := x\n', '@[simp] public theorem a : True := by trivial\n',
                         'attribute [simp] a\n', 'set_option maxHeartbeats 100 in\npublic theorem b : True := by trivial\n'):
            new = old + addition if not addition.startswith('@') else old.replace('public theorem a : True := by sorry', addition)
            self.assertTrue(s3.reader_risks(old, new), addition)
        self.assertTrue(s3.reader_risks(old, old.replace('public import', 'import')))
        self.assertFalse(s3.reader_risks(None, old + 'instance myInst : X := x\n'))
        self.assertFalse(s3.reader_risks(old, old + 'local instance myInst : X := x\n'))
        self.assertFalse(s3.reader_risks(old, old + 'section\ninstance myInst : X := x\nattribute [local instance] myInst\nend\n'))
        self.assertTrue(s3.reader_risks(old, old + 'section\nattribute [local instance] myInst\nend\ninstance myInst : X := x\n'))
    def test_review_class_keeps_reader_risk(self):
        import review_class as rc
        old = 'module\npublic import Sheaf.B\npublic theorem a : True := by sorry\n'
        new = old + 'instance myInst : X := x\n'
        D = {'fails': [], 'nodes': {}, 'changes': {}, 'modules': [{'role': 'item', 'file': 'lean/Sheaf/A.lean',
             'module': 'Sheaf.A', 'old': old, 'text': new, 'diff': s3.diff_module(old, new)}]}
        with patch.object(rc, 'git', lambda *a: 'deadbeef'), patch.object(s3, 'importers', lambda m: []):
            cls, why, _ = rc.classify('TEST', 'Sheaf.A', D)
        self.assertEqual(cls, 'CODEX'); self.assertIn('global instance', why)

    def test_real_incident_and_three_ordinary_landings(self):
        root = pathlib.Path(__file__).resolve().parent.parent
        path = 'lean/WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/CohomologyPresheaf.lean'
        old, new = [br.blob(root, ref, path) for ref in ('316464bcc^', '316464bcc')]
        if old is None: self.skipTest('incident commit unavailable')
        risks = s3.reader_risks(old.decode(), new.decode())
        self.assertTrue(any('global instance' in r for r in risks)); self.assertTrue(any('public import' in r for r in risks))
        for sha in ('7145c5af0', '9552554e8', '8323bac32'):
            paths = br.git(root, 'diff-tree', '--no-commit-id', '--name-only', '-r', sha).decode().splitlines()
            mods = [p for p in paths if p.startswith('lean/') and p.endswith('.lean')]
            self.assertTrue(mods)
            for p in mods:
                a, b = br.blob(root, sha + '^', p), br.blob(root, sha, p)
                self.assertEqual(s3.reader_risks(a.decode() if a else None, b.decode()), [], sha)


if __name__ == '__main__': unittest.main()
