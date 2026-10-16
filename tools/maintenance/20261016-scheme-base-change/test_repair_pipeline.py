"""Source-only regressions; never start a dispatcher, worker, compiler, or SSH."""
import ast
import os
import pathlib
import tempfile
import types
import unittest


DISPATCHER = pathlib.Path(os.environ.get(
    'REPAIR_TEST_DISPATCHER', '/home/ubuntu/weil-launcher-all/dispatch_all.py'))
DELIVERY = pathlib.Path(os.environ.get(
    'REPAIR_TEST_DELIVERY', '/home/ubuntu/weil-launcher/deliver3.py'))
ITEM = 'Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap'


def load_seed_method():
    tree = ast.parse(DISPATCHER.read_text())
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'Group')
    method = next(n for n in cls.body if isinstance(n, ast.FunctionDef)
                  and n.name == 'sandbox_from_branch')
    namespace = {}
    exec(compile(ast.Module(body=[method], type_ignores=[]), str(DISPATCHER), 'exec'),
         namespace)
    return namespace['sandbox_from_branch'], namespace


class RepairSandboxTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.sb = self.root / 'V3' / ITEM
        self.sb.mkdir(parents=True)
        self.payload = {
            'lean/Sheaf/AlgebraicGeometry/SchemeDerivedBaseChangeMap.lean': 'rejected body',
            'dag/nodes/sec-test/definition.json': '{"old": true}',
            'coord/reports/V3/' + ITEM + '.md': 'rejected report',
        }
        self.calls = []
        self.method, self.ns = load_seed_method()

        def fake_git(clone, *args):
            self.calls.append(args)
            if args[0] == 'diff':
                return types.SimpleNamespace(returncode=0, stdout='\n'.join(self.payload))
            if args[0] == 'show':
                return types.SimpleNamespace(returncode=0,
                                             stdout=self.payload[args[1].split(':', 1)[1]])
            raise AssertionError(args)

        self.ns.update(git=fake_git, log=lambda *args: None,
                       sharedrepo=types.SimpleNamespace(fetch=lambda *args:
                           types.SimpleNamespace(returncode=0)))
        batch = types.SimpleNamespace(sandbox=lambda stage: self.root,
                                      c={'clone_prefix': 'test'}, main='sheaf-dag')
        self.group = types.SimpleNamespace(g='V3', b=batch, clone=self.root)

    def test_empty_sandbox_is_seeded(self):
        self.method(self.group, ITEM, '3')
        self.assertEqual((self.sb / next(iter(self.payload))).read_text(), 'rejected body')
        self.assertEqual((self.sb / 'report.md').read_text(), 'rejected report')

    def test_retry_preserves_work_in_every_stage(self):
        for stage in ('1', '2', '3'):
            with self.subTest(stage=stage):
                source = self.sb / next(iter(self.payload))
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('new fixed-witness work')
                report = self.sb / 'report.md'
                report.write_text('new repair report')
                self.method(self.group, ITEM, stage)
                self.assertEqual(source.read_text(), 'new fixed-witness work')
                self.assertEqual(report.read_text(), 'new repair report')
        self.assertEqual(self.calls, [])

    def test_existing_node_preserves_node_only_work(self):
        node = self.sb / 'dag/nodes/sec-test/definition.json'
        node.parent.mkdir(parents=True)
        node.write_text('{"repaired": true}')
        self.method(self.group, ITEM, '2')
        self.assertEqual(node.read_text(), '{"repaired": true}')
        self.assertEqual(self.calls, [])

    def test_failed_fetch_does_not_write(self):
        self.ns['sharedrepo'].fetch = lambda *args: types.SimpleNamespace(returncode=1)
        self.method(self.group, ITEM, '3')
        self.assertEqual(list(self.sb.iterdir()), [])


class ReturnedRepairGateTests(unittest.TestCase):
    def run_gate(self, item, returned):
        tree = ast.parse(DELIVERY.read_text())
        main = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
        block = next(n for n in main.body if isinstance(n, ast.If)
                     and any(isinstance(x, ast.Assign) and any(
                         isinstance(t, ast.Name) and t.id == 'closed' for t in x.targets)
                             for x in n.body))
        gate = next(n for n in block.body if isinstance(n, ast.Try)
                    and 'listed_repair' in ast.unparse(n))
        reject = next(n for n in block.body if isinstance(n, ast.If)
                      and 'not listed_repair' in ast.unparse(n.test))
        with tempfile.TemporaryDirectory() as tmp:
            clone = pathlib.Path(tmp)
            (clone / 'coord/returns').mkdir(parents=True)
            (clone / 'coord/repairs.txt').write_text('')
            (clone / 'coord/returns/V3.md').write_text(returned)
            ns = dict(clone=clone, g='V3', item=item, closed=[],
                      d={'disputed_new': False, 'statement_changed': False, 'sorry_before': []},
                      s3=types.SimpleNamespace())
            exec(compile(ast.Module(body=[gate, reject], type_ignores=[]),
                         str(DELIVERY), 'exec'), ns)

    def test_returned_zero_hole_repair_is_accepted(self):
        self.run_gate(ITEM, '## ' + ITEM + ' (2026-10-14, branch head bee6a8e503)\nE3\n')

    def test_unrelated_zero_hole_delivery_is_rejected(self):
        with self.assertRaisesRegex(SystemExit, 'nothing is proved'):
            self.run_gate(ITEM, '## Sheaf.Other (branch head abc123456)\n')


if __name__ == '__main__':
    unittest.main()
