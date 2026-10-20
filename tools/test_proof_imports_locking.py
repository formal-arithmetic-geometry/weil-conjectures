"""Exercise the deployed import writer with real locks in an isolated repository."""
import os
import pathlib
import signal
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = pathlib.Path(__file__).resolve().parent.parent


class ProofImportLocks(unittest.TestCase):
    def run_writer(self, cycle):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            for name in ("coord", "local", "tools", "lean/Sheaf", "work"):
                (root / name).mkdir(parents=True, exist_ok=True)
            target = root / "lean/Sheaf/A.lean"
            target.write_text("module\npublic theorem a : True := by sorry\n")
            (root / "work/cycle.json").write_text("{}")
            writer = textwrap.dedent(f"""\
                import fcntl, pathlib, sys
                sys.path.insert(0, {str(ROOT / 'tools')!r})
                import add_proof_imports as api
                import landing
                root = pathlib.Path.cwd()
                api.li.ROOT = root
                api.li.LEAN = root / 'lean'
                landing.LOCAL = root / 'local'
                landing.merge_queue = lambda: True

                def assert_locked():
                    with (root / 'local/tree.lock').open('a') as f:
                        try:
                            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError:
                            return
                    raise AssertionError('writer does not own tree.lock')

                def file_of(module):
                    assert_locked()
                    return root / 'lean' / (module.replace('.', '/') + '.lean')

                def record(*args, **kwargs):
                    assert_locked()
                    assert 'import Sheaf.B' in (root / 'lean/Sheaf/A.lean').read_text()
                    (root / 'recorded').touch()

                api.li.file_of = file_of
                landing.new_record = record
                assert api.write([('Sheaf.A', 'Sheaf.B', [], '')], False) == 1
                """)
            (root / "tools/add_proof_imports.py").write_text(writer)
            if cycle:
                # Run the actual wrapper's lock/application block, with its writer
                # redirected into this fixture. Do not run its compilation phase.
                text = (ROOT / "deployment/proof-imports-cycle.sh").read_text()
                block = text[text.index("exec 8>> coord/.merge.lock;"):text.index("mapfile -t MODS")]
                command = ["bash", "-c", "set -uo pipefail\nsay() { echo \"$*\"; }\n" + block]
            else:
                command = [sys.executable, "tools/add_proof_imports.py"]
            env = dict(os.environ, W=str(root / "work"), J=str(root / "work/cycle.json"))
            process = subprocess.Popen(command, cwd=root, env=env, start_new_session=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                # Only the fixture processes started by this test are terminated.
                os.killpg(process.pid, signal.SIGTERM)
                process.communicate()
                self.fail("proof-import writer deadlocked under the cycle wrapper")
            self.assertEqual(process.returncode, 0, stdout + stderr)
            self.assertIn("import Sheaf.B", target.read_text())
            self.assertTrue((root / "recorded").exists())

    def test_cycle_and_writer_do_not_reacquire_tree_lock(self):
        self.run_writer(cycle=True)

    def test_writer_holds_tree_lock_for_mutation_and_record(self):
        self.run_writer(cycle=False)

if __name__ == "__main__":
    unittest.main()
