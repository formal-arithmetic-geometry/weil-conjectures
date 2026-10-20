"""Pipelined batch landing (SHEAF_PIPELINE_BATCHES, 2026-10-21): batch N+1 lands while the build of batch N runs.
Pure Python/git; the global build is an oracle (a landing is bad or not); no Lean command runs.
Run: cd tools && python3 -m unittest test_pipeline_batches"""
import contextlib, hashlib, json, os, pathlib, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0, str(pathlib.Path(__file__).parent))
os.environ["SHEAF_LEAD"] = "L-only"
import batch_recovery as br
import batch_land as bl
import landing as ld


class Pipeline(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.g('init', '-q'); self.g('config', 'user.email', 'test@example.invalid'); self.g('config', 'user.name', 'test')
        self.put('.gitignore', 'local/\nalerts/\n')
        self.put('coord/ledger.md', 'ledger\n'); self.put('coord/deliveries.log', 'log\n')
        for i in range(10):
            self.put(f'lean/Sheaf/D{i}.lean', f'module\npublic theorem value{i} : True := by sorry\n')
        self.put('lean/Sheaf/Old.lean', 'module\nimport Sheaf.D1\nimport Sheaf.D6\npublic theorem old : True := by trivial\n')
        self.commit('base')
        self.local = self.root / 'local'; self.builds = self.local / 'builds'
        for d in ('requests', 'done', 'backup', 'staged', 'inflight'): (self.builds / d).mkdir(parents=True)
        self.seq = 0; self.logs = []; self.cur = None; self.next_landed = []; self.calls = []

    def g(self, *a): return br.git(self.root, *a).decode().strip()
    def put(self, path, data):
        p = self.root / path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(data)
    def commit(self, msg): self.g('add', '.'); self.g('commit', '-qm', msg); return self.g('rev-parse', 'HEAD')

    def land(self, group, i, file_index=None, text=None):
        """One delivery written, committed and recorded as a landing (as land_one does, merge-queue records)."""
        fi = i if file_index is None else file_index
        rel = f'Sheaf/D{fi}.lean'
        before = (self.root / 'lean' / rel).read_text()
        after = text or f'module\npublic theorem value{fi} : True := by trivial -- {group}{i}\n'
        if i in self.iface: after += f'public theorem extra{i} : True := by trivial\n'
        self.put('lean/' + rel, after)
        sha = self.commit(f'Prove D{i} ({group})')
        lid = f'{group}{i:02d}'
        self.seq += 1
        for d, t in (('backup', before), ('staged', after)):
            q = self.builds / d / lid / rel; q.parent.mkdir(parents=True, exist_ok=True); q.write_text(t)
        ld.write_json(self.builds / 'requests' / f'{lid}.json', dict(
            id=lid, group='L', seq=self.seq, kind='interface', batch='x',
            files=[dict(path=rel, module=f'Sheaf.D{fi}', existed=True, sha=hashlib.sha256(after.encode()).hexdigest())]))
        return dict(group=group, item=f'Sheaf.D{i}', head=sha, commit=sha, landing=lid, state='landed',
                    modules=[f'Sheaf.D{fi}'], kind='interface', reviewer='test', claim=None)

    def run_scenario(self, bad=(), overlap=None, pipeline=True, has_interface=True, fail_as=None, iface=()):
        """Batch N = G0..G4 lands; the first build starts; the lander steps (pipelining H5..H9 as batch N+1); the build
        ends (red when it contains a bad landing still open: the failing module is that landing's module); and so on.
        overlap=(i, j): the landing H<i> of N+1 rewrites the file of G<j> of N."""
        self.iface = set(iface)
        n_entries = [self.land('G', i) for i in range(5)]
        b = dict(id='N', time=ld.now(), round=0, handled=[], entries=n_entries)

        def fake_land_batch(cache, log, target=None):
            self.calls.append(target)
            if target != bl.NEXT or self.next_landed:
                return None
            es = []
            for i in range(5, 10):
                if overlap and overlap[0] == i:
                    es.append(self.land('H', i, file_index=overlap[1],
                                        text=f'module\npublic theorem value{overlap[1]} : True := by trivial -- H{i} on top\n'))
                else:
                    es.append(self.land('H', i))
            nb = dict(id='N1', time=ld.now(), round=0, handled=[], entries=es, pipelined_on='N')
            bl.write_json(bl.NEXT, nb); self.next_landed = es
            return nb

        def running():
            return None if self.cur is None or self.cur.get('finished') else self.cur

        ps = [patch.object(ld, 'merge_queue', lambda: True), patch.object(ld, 'BACKUP', self.builds / 'backup'),
              patch.object(ld, 'STAGED', self.builds / 'staged'), patch.object(ld, 'INFLIGHT', self.builds / 'inflight'),
              patch.object(ld, 'LOCAL', self.local), patch.object(ld, 'B', self.builds), patch.object(ld, 'WORK', self.root / 'coord'),
              patch.object(ld, 'REQUESTS', self.builds / 'requests'), patch.object(ld, 'DONE', self.builds / 'done'),
              patch.object(ld.li, 'LEAN', self.root / 'lean'),
              patch.object(bl, 'MQ_LOG', lambda x: self.logs.append(('MQ', x))),
              patch.object(bl, 'ROOT', self.root), patch.object(bl.md, 'ROOT', self.root),
              patch.object(bl.repairs, 'ROOT', self.root), patch.object(bl.repairs, 'JOBS', self.local / 'batch/repair'),
              patch.object(bl, 'BD', self.local / 'batch'), patch.object(bl, 'OPEN', self.local / 'batch/open.json'),
              patch.object(bl, 'NEXT', self.local / 'batch/next.json'), patch.object(bl, 'CLOSED', self.local / 'batch/closed'),
              patch.object(bl, 'PASSED', self.local / 'batch/passed'),
              patch.object(bl.md, 'merge_lock', lambda: contextlib.nullcontext()), patch.object(bl, 'refresh_recovery_queue'),
              patch.object(bl, 'candidates', lambda cache: []), patch.object(bl, 'land_batch', fake_land_batch),
              patch.object(bl, 'pipeline_on', lambda: pipeline), patch.object(bl, 'running_build', running),
              patch.dict(os.environ, {'SHEAF_ALERT_DIR': str(self.root / 'alerts')})]
        results = []
        with contextlib.ExitStack() as stack:
            for p in ps: stack.enter_context(p)
            bl.write_json(bl.OPEN, b)
            step = lambda: bl.step({'_pre': type('Pre', (), {'pump': lambda *a: None})()}, lambda *x: self.logs.append(x))
            bad_ids = set(bad)
            for n in range(8):
                included = sorted(r['id'] for r in ld.records(ld.REQUESTS))
                if not included and not bl.OPEN.exists() and not bl.NEXT.exists():
                    break
                self.cur = dict(time=str(n), included=included, has_interface=has_interface, pid=os.getpid(), mode='')
                for _ in range(2): step()               # during the build: the pipelined batch may land
                still = {r['id']: r for r in ld.records(ld.REQUESTS)}
                broken = [i for i in included if i in bad_ids and i in still]
                if broken:
                    last = dict(time=str(n), result='red', included=included, batch_checks=[],
                                failing=[fail_as] if fail_as else sorted({f['module'] for i in broken for f in still[i]['files']}),
                                errors=['error: type mismatch'])
                else:
                    for i in included:
                        if i in still:
                            ld.write_json(ld.DONE / f'{i}.json', dict(still[i], result='verified', commit='c' * 40))
                            (ld.REQUESTS / f'{i}.json').unlink()
                    last = dict(time=str(n), result='green', included=included)
                results.append((last['result'], included))
                ld.write_json(self.builds / 'last.json', last)
                self.cur = dict(self.cur, finished='yes')
                for _ in range(3): step()
            else:
                self.fail('did not finish: ' + repr(self.logs)[-3000:])
            self.assertFalse(bl.OPEN.exists()); self.assertFalse(bl.NEXT.exists())
            closed = {p.stem: bl.read_json(p) for p in sorted(bl.CLOSED.glob('*.json'))}
        states = {e['landing']: e['state'] for c in closed.values() for e in c['entries']}
        return closed, states, results

    def assert_all_other_verified(self, states, out):
        self.assertEqual(len(states), 10, states)
        for k, v in states.items():
            self.assertEqual(v, 'returned' if k in out else 'verified', (k, states))
        rets = (self.root / 'coord/returns').glob('*.md')
        text = ''.join(p.read_text() for p in rets)
        for k in states:
            if k not in out:     # a good delivery is never returned
                self.assertNotIn(f'value{int(k[1:])} : True := by trivial -- {k}', text)

    def test_pipelined_batch_lands_during_the_build_and_both_verify(self):
        closed, states, results = self.run_scenario()
        self.assertEqual([r for r, _ in results], ['green', 'green'])
        self.assertEqual(results[0][1], ['G00', 'G01', 'G02', 'G03', 'G04'])           # N+1 not in the first build
        self.assertEqual(results[1][1], ['H05', 'H06', 'H07', 'H08', 'H09'])
        self.assertEqual(sorted(closed), ['N', 'N1'])
        self.assert_all_other_verified(states, set())

    def test_red_in_n_only(self):
        closed, states, results = self.run_scenario(bad=('G01',))
        self.assertEqual([r for r, _ in results], ['red', 'green'])
        self.assertEqual(sorted(closed), ['N'])                  # N+1 folded into N for the recovery
        self.assertEqual(closed['N']['folded'], ['N1'])
        self.assert_all_other_verified(states, {'G01'})
        self.assertIn('sorry', (self.root / 'lean/Sheaf/D1.lean').read_text())

    def test_red_in_n_plus_1_only(self):
        closed, states, results = self.run_scenario(bad=('H07',))
        self.assertEqual([r for r, _ in results], ['green', 'red', 'green'])
        self.assertEqual(sorted(closed), ['N', 'N1'])
        self.assert_all_other_verified(states, {'H07'})

    def test_red_in_both(self):
        closed, states, results = self.run_scenario(bad=('G02', 'H08'))
        self.assertEqual([r for r, _ in results], ['red', 'red', 'green'])
        self.assertEqual(closed['N']['round'], 2)
        self.assert_all_other_verified(states, {'G02', 'H08'})

    def test_n_plus_1_edits_a_file_of_n_and_n_is_bad(self):
        # H06 rewrote D3 after G03 landed it; G03 is red: H06 goes out with it (fully undone), the rest verifies
        closed, states, results = self.run_scenario(bad=('G03',), overlap=(6, 3))
        self.assertEqual([r for r, _ in results], ['red', 'green'])
        self.assert_all_other_verified(states, {'G03', 'H06'})
        self.assertEqual((self.root / 'lean/Sheaf/D3.lean').read_text(), 'module\npublic theorem value3 : True := by sorry\n')
        self.assertTrue(any('goes out with the culprit' in str(x) for x in self.logs))

    def test_n_plus_1_edits_a_file_of_n_and_is_bad_itself(self):
        # G03 verified by the first build; H06's own version of D3 is red: D3 goes back to G03's version, not further
        closed, states, results = self.run_scenario(bad=('H06',), overlap=(6, 3))
        self.assertEqual([r for r, _ in results], ['green', 'red', 'green'])
        self.assert_all_other_verified(states, {'H06'})
        self.assertIn('-- G3', (self.root / 'lean/Sheaf/D3.lean').read_text())

    def test_n_plus_1_edits_a_file_of_n_all_good(self):
        closed, states, results = self.run_scenario(overlap=(6, 3))
        self.assertEqual([r for r, _ in results], ['green', 'green'])
        self.assert_all_other_verified(states, set())
        self.assertIn('-- H6 on top', (self.root / 'lean/Sheaf/D3.lean').read_text())

    def test_red_importer_blames_only_landings_the_build_contained(self):
        # Sheaf.Old imports D1 (G01, in the build) and D6 (H06, landed after the build's snapshot): only G01 is a suspect
        closed, states, results = self.run_scenario(bad=('G01',), fail_as='Sheaf.Old', iface=(1, 6))
        self.assertEqual([r for r, _ in results], ['red', 'green'])
        self.assert_all_other_verified(states, {'G01'})

    def test_switch_off_lands_nothing_during_the_build(self):
        closed, states, results = self.run_scenario(pipeline=False)
        self.assertEqual(self.next_landed, [])
        self.assertNotIn(bl.NEXT, self.calls)

    def test_no_pipelining_on_a_build_without_interface_landing(self):
        self.run_scenario(has_interface=False)
        self.assertEqual(self.next_landed, [])


if __name__ == '__main__':
    unittest.main()
