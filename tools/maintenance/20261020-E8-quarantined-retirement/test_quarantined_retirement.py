"""Test the deployed deliver3 manifest parser without imports, compiles or network.

The parser is extracted from main by syntax, so these checks exercise the actual
deployed path checks rather than a second implementation of them.
"""
import ast
from pathlib import Path
import tempfile
import unittest


SOURCE = Path(__file__).with_name('deliver3.py')
tree = ast.parse(SOURCE.read_text())
main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main')
start = next(i for i, node in enumerate(main.body) if isinstance(node, ast.Assign)
             and isinstance(node.targets[0], ast.Name) and node.targets[0].id == 'deleted')
stop = next(i for i, node in enumerate(main.body) if isinstance(node, ast.Assign)
            and isinstance(node.targets[0], ast.Name) and node.targets[0].id == 'own_deleted')
parser = compile(ast.Module(body=main.body[start:stop], type_ignores=[]), str(SOURCE), 'exec')


class QuarantinedRetirement(unittest.TestCase):
    item = 'Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions'
    relative = 'lean/' + item.replace('.', '/') + '.lean'
    quarantine = 'quarantine/' + item.replace('.', '/') + '.lean'

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.clone = Path(self.tmp.name) / 'clone'
        self.sb = Path(self.tmp.name) / 'sandbox'
        self.sb.mkdir()
        self.write(self.sb, 'deleted.txt', self.relative + '\n')

    @staticmethod
    def write(root, name, text):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def read(self):
        namespace = {'clone': self.clone, 'sb': self.sb}
        exec(parser, namespace)
        return namespace['deleted']

    def test_quarantined_withdrawal_preserves_original(self):
        self.write(self.clone, self.quarantine, 'module\n-- preserved original\n')
        original = (self.clone / self.quarantine).read_bytes()
        self.assertEqual(self.read(), [self.relative])
        self.assertEqual((self.clone / self.quarantine).read_bytes(), original)
        self.assertFalse((self.clone / self.relative).exists())

    def test_live_withdrawal_unchanged(self):
        self.write(self.clone, self.relative, 'module\n')
        self.assertEqual(self.read(), [self.relative])

    def test_missing_source_rejected(self):
        with self.assertRaisesRegex(SystemExit, 'neither on sheaf-dag nor in quarantine'):
            self.read()

    def test_present_sandbox_source_rejected(self):
        self.write(self.clone, self.quarantine, 'module\n')
        self.write(self.sb, self.relative, 'module\n')
        with self.assertRaisesRegex(SystemExit, 'still present in the sandbox'):
            self.read()

    def test_nonlean_and_traversal_paths_rejected(self):
        for name in ['coord/rework.tsv', 'quarantine/Sheaf/A.lean', 'lean/../Sheaf/A.lean']:
            with self.subTest(name=name):
                self.write(self.sb, 'deleted.txt', name + '\n')
                with self.assertRaisesRegex(SystemExit, 'may list only lean'):
                    self.read()

    def test_comments_and_empty_lines(self):
        self.write(self.clone, self.quarantine, 'module\n')
        self.write(self.sb, 'deleted.txt', '# retirement\n\n' + self.relative + '\n')
        self.assertEqual(self.read(), [self.relative])

    def test_no_manifest(self):
        (self.sb / 'deleted.txt').unlink()
        self.assertEqual(self.read(), [])


if __name__ == '__main__':
    unittest.main(verbosity=2)
