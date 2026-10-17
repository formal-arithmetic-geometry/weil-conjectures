"""Check the deployed resume selector without importing runtime admission code."""
import ast
import os
from pathlib import Path
import re
import unittest


SOURCE = Path(os.environ.get("CODEX_RETRY_SOURCE", Path(__file__).with_name("codex_retry.py")))
TREE = ast.parse(SOURCE.read_text())
HELPERS = [n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name in
           {"resume_session", "requested_session", "output_path", "resume_args"}]
ns = {"Path": Path, "re": re, "RUN": Path("/unused/run")}
exec(compile(ast.Module(body=HELPERS, type_ignores=[]), str(SOURCE), "exec"), ns)
selector = ns.get("resume_session", ns.get("requested_session"))
SID = "01a14716-9aa0-7193-af70-4bb9c50e6016"


class ResumeSelector(unittest.TestCase):
    def setUp(self):
        self.root = Path("/unused/run")
        self.last = self.root / "E1/Cube.123/last.txt"
        self.args = ["exec", "resume", "-m", "same-model", "-o", str(self.last), SID, "-"]

    def test_explicit_session_is_supervised(self):
        self.assertEqual(selector(self.args), SID)
        self.assertEqual(ns["output_path"](self.args, self.root), self.last)

    def test_shared_last_selector_always_bypasses_supervision(self):
        for args in ([*self.args[:2], "--last", *self.args[2:]],
                     [*self.args[:-2], "--last", "-"]):
            with self.subTest(args=args):
                self.assertIsNone(selector(args))
                self.assertIsNone(ns["output_path"](args, self.root))

    def test_stdin_marker_is_required(self):
        self.assertIsNone(selector([*self.args[:-1], "some prompt"]))

    def test_resume_keeps_model_and_replaces_only_session(self):
        other = "01a14740-f2eb-7510-b1d9-72278909b7b3"
        result = ns["resume_args"](self.args, other)
        self.assertEqual(result, [*self.args[:-2], other, "-"])


if __name__ == "__main__":
    unittest.main()
