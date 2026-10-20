"""Exercise the actual delivery helper without Lean, SSH, claims or git writes."""
import ast
import os
import pathlib
import re
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

SOURCE = pathlib.Path(os.environ.get("DELIVER3_SOURCE", pathlib.Path(__file__).with_name("deliver3.py")))
TREE = ast.parse(SOURCE.read_text())
FUNCTION = next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == "forced_adaptations")


class RetirementCounterfactual(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.clone = self.root / "clone"
        self.sb = self.root / "sandbox"
        self.rel = pathlib.Path("lean/Sheaf/Consumer.lean")
        self.old = self.clone / self.rel
        self.new = self.sb / self.rel
        self.old.parent.mkdir(parents=True)
        self.new.parent.mkdir(parents=True)
        (self.sb / ".lbuild").mkdir()
        self.old.write_text("module\npublic import Sheaf.Retired\npublic theorem result : True := by trivial\n")
        self.new.write_text("module\npublic import WeilConjectures.Retired\npublic theorem result : True := by simp\n")
        self.s3 = types.SimpleNamespace(claim_holder=lambda _: "other", diff_module=lambda *_: {})
        ns = dict(pathlib=pathlib, re=re, tempfile=tempfile, scrub=lambda s: s,
                  lcompile=types.SimpleNamespace(modname=lambda p: ".".join(p.relative_to(p.parents[1]).with_suffix("").parts)))
        exec(compile(ast.Module(body=[FUNCTION], type_ignores=[]), str(SOURCE), "exec"), ns)
        self.helper = ns["forced_adaptations"]
        self.calls = []

    def compile(self, src):
        self.calls.append((src.read_text(), (src.parents[2] / ".lbuild").exists()))
        return 0, ""

    def run_helper(self, **kwargs):
        with patch.dict(sys.modules, stage3_delivery=self.s3):
            return self.helper(self.clone, self.sb, "Sheaf.Retired", [self.new], group="A9",
                               compile_one=kwargs.pop("compile_one", self.compile), **kwargs)

    def test_migration_has_explicit_evidence_without_stale_baseline_compile(self):
        text = self.run_helper(deleted=["lean/Sheaf/Retired.lean"])
        self.assertIn("Sheaf.Consumer", text)
        self.assertIn("explicitly withdrawn in deleted.txt: Sheaf.Retired", text)
        self.assertIn("CODEX verifies", text)
        self.assertEqual(self.calls, [])

    def test_no_manifest_still_rejects_unforced_change(self):
        with self.assertRaisesRegex(SystemExit, "adaptation is not forced"):
            self.run_helper()
        self.assertEqual(len(self.calls), 2)

    def test_unrelated_deletion_does_not_exempt_consumer(self):
        with self.assertRaisesRegex(SystemExit, "adaptation is not forced"):
            self.run_helper(deleted=["lean/Sheaf/Other.lean"])

    def test_remaining_withdrawn_import_is_not_exempt(self):
        self.new.write_text(self.old.read_text().replace("by trivial", "by simp"))
        with self.assertRaisesRegex(SystemExit, "adaptation is not forced"):
            self.run_helper(deleted=["lean/Sheaf/Retired.lean"])

    def test_another_withdrawn_import_is_not_exempt(self):
        self.new.write_text(self.new.read_text() + "public import Sheaf.Other\n")
        with self.assertRaisesRegex(SystemExit, "adaptation is not forced"):
            self.run_helper(deleted=["lean/Sheaf/Retired.lean", "lean/Sheaf/Other.lean"])

    def test_real_dependency_error_still_records_both_compiles(self):
        def compile_one(src):
            overlay = (src.parents[2] / ".lbuild").exists()
            return (1, "error: changed API") if overlay else (0, "")
        self.assertIn("error: changed API", self.run_helper(compile_one=compile_one))

    def test_bad_baseline_and_inconclusive_failures_still_reject(self):
        for failure in [(124, "timeout"), (1, "unknown module prefix Sheaf"),
                        (1, "error: object file X does not exist"), (1, "no diagnostic")]:
            with self.subTest(failure=failure):
                calls = []
                def compile_one(src):
                    calls.append(src)
                    return (0, "") if len(calls) == 1 else failure
                with self.assertRaisesRegex(SystemExit, "cannot establish forced adaptation"):
                    self.run_helper(compile_one=compile_one)
        with self.assertRaisesRegex(SystemExit, "already fails against the compiled baseline"):
            self.run_helper(compile_one=lambda _: (1, "error: baseline broken"))

    def test_same_holder_and_unchanged_sources_keep_existing_exceptions(self):
        self.s3.claim_holder = lambda _: "A9"
        self.assertEqual(self.run_helper(), "")
        self.s3.claim_holder = lambda _: "other"
        self.new.write_text(self.old.read_text())
        self.assertEqual(self.run_helper(), "")
        self.assertEqual(self.calls, [])

    def test_main_passes_validated_deletion_manifest(self):
        main = next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == "main")
        calls = [n for n in ast.walk(main) if isinstance(n, ast.Call) and
                 isinstance(n.func, ast.Name) and n.func.id == "forced_adaptations"]
        self.assertEqual(len(calls), 1)
        self.assertTrue(any(k.arg == "deleted" and isinstance(k.value, ast.Name) and
                            k.value.id == "deleted" for k in calls[0].keywords))


if __name__ == "__main__":
    unittest.main()
