#!/usr/bin/env python3
"""tools/quarantine_wait.py on a mock tree: a delivery missing only quarantined imports waits (capped), one missing a
module that never existed is returned; holding() releases it when the import is back in lean/.
Run: python3 tools/test_quarantine_wait.py"""
import os, pathlib, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ["SHEAF_LEAD"] = "L-only"
import import_cycles as ic  # noqa: E402
import quarantine_wait as qw  # noqa: E402


class QuarantineWait(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="qwait-test-")
        R = self.root = pathlib.Path(self.tmp.name)
        (R / "quarantine/Sheaf").mkdir(parents=True); (R / "lean/Sheaf").mkdir(parents=True); (R / "coord").mkdir()
        (R / "quarantine/Sheaf/Q.lean").write_text("module\n")
        (R / "coord/rework.tsv").write_text("# header\nSheaf.R\tlean/Sheaf/R.lean\tquarantine/Sheaf/R.lean\tbuild\tt\tc\t\t\n")
        self.patches = [patch.object(qw, "ROOT", R), patch.object(qw, "STATE", R / "local/batch/qw.json"),
                        patch.object(qw.rework, "ROOT", R), patch.object(qw.rework, "FILE", R / "coord/rework.tsv")]
        for p in self.patches: p.start()

    def tearDown(self):
        for p in self.patches: p.stop()
        self.tmp.cleanup()

    def missing(self, text):
        with self.assertRaises(ic.MissingImports) as cm:
            ic.refuse_missing({"Sheaf.A": text}, {"Sheaf.Base"}, [])
        self.assertIn("missing import source modules: Sheaf.A:", str(cm.exception))
        return cm.exception

    def test_quarantined_waits_then_cap_returns(self):
        exc = self.missing("module\nimport Sheaf.Base\nimport Sheaf.Q\nimport Sheaf.R\n")
        w = qw.wait(exc, "G1", "Sheaf.A", "h1", now=1000.0)
        self.assertTrue(w.startswith("waits: imports quarantined Sheaf.Q, Sheaf.R"), w)
        self.assertTrue(qw.holding("h1", now=1000.0 + 60))
        self.assertIsNotNone(qw.wait(exc, "G1", "Sheaf.A", "h1", now=1000.0 + 5 * 3600))   # since is kept
        self.assertIsNone(qw.wait(exc, "G1", "Sheaf.A", "h1", now=1000.0 + 6 * 3600))      # cap: returned as before
        self.assertNotIn("h1", qw.load())

    def test_restore_releases_and_lagging_tip_still_waits(self):
        exc = self.missing("module\nimport Sheaf.Q\n")
        self.assertIsNotNone(qw.wait(exc, "G1", "Sheaf.A", "h2", now=0.0 + 1))
        self.assertTrue(qw.holding("h2", now=2.0))
        (self.root / "lean/Sheaf/Q.lean").write_text("module\n")          # restored in the working tree
        self.assertFalse(qw.holding("h2", now=3.0))                        # checked again
        self.assertIsNotNone(qw.wait(exc, "G1", "Sheaf.A", "h2", now=4.0)) # library tip not yet with it: still waits
        qw.prune(set())
        self.assertEqual(qw.load(), {})

    def test_genuinely_missing_returns_now(self):
        exc = self.missing("module\nimport Sheaf.Q\nimport Sheaf.Ghost\n")
        self.assertIsNone(qw.wait(exc, "G1", "Sheaf.A", "h3", now=1.0))
        self.assertFalse(qw.holding("h3", now=2.0))
        self.assertIsNone(qw.wait(RuntimeError("other"), "G1", "Sheaf.A", "h3"))


if __name__ == "__main__":
    unittest.main()
