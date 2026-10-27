"""Source-reader regressions for the stale Package artifact seen by group ND."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import nt_compile_source as reader
import nt_source_overlay as overlay


OLD = "module\n\n@[expose] public section\ndef value : Nat := 1\n"
NEW = OLD.replace(":= 1", ":= 2") + "def extra : Nat := 3\n"


class CompileSourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.module = "Sheaf.Test.Package"
        self.rel = "lean/Sheaf/Test/Package.lean"
        self.source = self.root / self.rel
        self.source.parent.mkdir(parents=True)
        self.source.write_text(OLD)
        (self.root / "lean/lakefile.toml").write_text('name = "test"\n')
        self.artifact = self.root / "lean/.lake/build/lib/lean/Sheaf/Test/Package.olean"
        self.artifact.parent.mkdir(parents=True)
        self.artifact.write_bytes(b"published artifact")
        self.git("init", "-q")
        self.git("add", self.rel, "lean/lakefile.toml")
        self.commit()
        self.published = self.git("rev-parse", "HEAD").strip()
        self.metadata = self.root / "local/builds/published.json"
        self.metadata.parent.mkdir(parents=True)
        self.metadata.write_text(json.dumps({"commit": self.published}))
        self.source.write_text(NEW)
        self.git("add", self.rel)
        self.commit()
        overlay._HEADER_CONVERSIONS.clear()
        overlay._UNBUILT.clear()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True,
                                       stderr=subprocess.PIPE)

    def commit(self):
        self.git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com",
                 "commit", "-qm", "fixture")

    def test_committed_modification_reads_current_source(self):
        # 2026-10-25 (deliverfix): the compiler uses the committed modification, so the reader shows it
        text, origin = reader.read_source(self.root, self.module)
        self.assertEqual(text, NEW)

    def test_missing_artifact_reads_current_private_source(self):
        self.artifact.unlink()
        text, origin = reader.read_source(self.root, self.module)
        self.assertEqual(text, NEW)
        self.assertIn("private compilation", origin)

    def test_header_conversion_reads_current_private_source(self):
        legacy = "import Mathlib.Data.Nat.Basic\n\ndef value : Nat := 1\n"
        converted = "module\n\npublic import Mathlib.Data.Nat.Basic\n\n@[expose] public section\n\ndef value : Nat := 1\n"
        self.source.write_text(legacy)
        self.git("add", self.rel)
        self.commit()
        self.metadata.write_text(json.dumps({"commit": self.git("rev-parse", "HEAD").strip()}))
        self.source.write_text(converted)
        self.git("add", self.rel)
        self.commit()
        self.assertEqual(reader.read_source(self.root, self.module)[0], converted)

    def test_unknown_published_source_fails_instead_of_using_working_tree(self):
        self.metadata.write_text(json.dumps({"commit": "missing-published-commit"}))
        with self.assertRaisesRegex(reader.SourceUnavailable, "refusing to substitute"):
            reader.read_source(self.root, self.module)

    def test_new_publication_reads_new_signature(self):
        self.metadata.write_text(json.dumps({"commit": self.git("rev-parse", "HEAD").strip()}))
        self.assertEqual(reader.read_source(self.root, self.module)[0], NEW)

    def test_mathlib_uses_package_source(self):
        path = self.root / "lean/.lake/packages/mathlib/Mathlib/Test.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- Mathlib source\n")
        self.assertEqual(reader.read_source(self.root, "Mathlib.Test")[0], path.read_text())

    def test_invalid_module_rejected(self):
        with self.assertRaises(reader.SourceUnavailable):
            reader.read_source(self.root, "Sheaf.Test/../../etc/passwd")


if __name__ == "__main__":
    unittest.main()
