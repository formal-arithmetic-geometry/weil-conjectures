"""Compiler-only repairs must expire cached diagnostics; no Lean runs."""
import argparse
import ast
from pathlib import Path
import subprocess
import tempfile
import time
import unittest


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lcompile", type=Path,
                    default=Path.home() / "weil-launcher/lcompile.py")
args, remaining = parser.parse_known_args()
tree = ast.parse(args.lcompile.read_text())
function = next(node for node in tree.body
                if isinstance(node, ast.FunctionDef) and node.name == "_source_tree")
code = compile(ast.Module(body=[function], type_ignores=[]), str(args.lcompile), "exec")


class CompilerCache(unittest.TestCase):
    def test_compiler_repairs_invalidate_without_lean_or_publication_change(self):
        with tempfile.TemporaryDirectory(prefix="lcompile-compiler-cache-test-") as directory:
            task_home = Path(directory)
            repo = task_home / "weil-conjectures-sheaf-shared"
            (repo / "lean").mkdir(parents=True)
            (repo / "tools").mkdir()
            (repo / "lean/Test.lean").write_text("module\n")
            for name in ("remote_compile_dependencies.py", "remote_compile_set.py"):
                (repo / "tools" / name).write_text("# original\n")

            def git(*command):
                return subprocess.check_output(["git", *command], cwd=repo, text=True).strip()

            def commit():
                git("add", ".")
                git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                    "commit", "-qm", "fixture")

            git("init", "-q")
            commit()
            context = {"H": task_home, "subprocess": subprocess, "time": time}
            exec(code, context)
            source_tree = context["_source_tree"]
            lean_tree, previous = git("rev-parse", "HEAD:lean"), source_tree()
            for name in ("remote_compile_dependencies.py", "remote_compile_set.py"):
                (repo / "tools" / name).write_text("# repaired\n")
                commit()
                self.assertEqual(lean_tree, git("rev-parse", "HEAD:lean"))
                current = source_tree()
                self.assertNotEqual(previous, current)
                previous = current
            (repo / "README.md").write_text("metadata only\n")
            commit()
            self.assertEqual(previous, source_tree())


if __name__ == "__main__":
    unittest.main(argv=[__file__, *remaining])
