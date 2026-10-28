#!/usr/bin/env python3
"""Tests of tools/setbuild.py (set builds, 2026-10-28): the pure parts."""
import json, pathlib, sys, tempfile, unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import setbuild as sb  # noqa: E402


class T(unittest.TestCase):
    def test_texts_sha(self):
        a = sb.texts_sha({"Sheaf/A.lean": "x", "Sheaf/B.lean": None})
        self.assertEqual(a, sb.texts_sha({"Sheaf/B.lean": None, "Sheaf/A.lean": "x"}))
        self.assertNotEqual(a, sb.texts_sha({"Sheaf/A.lean": "x", "Sheaf/B.lean": ""}))

    def test_eligible(self):
        self.assertTrue(sb.eligible({"statement_unchanged": True, "downstream_affected": False}))
        self.assertFalse(sb.eligible({"statement_unchanged": True, "downstream_affected": True}))
        self.assertFalse(sb.eligible({"statement_unchanged": False, "downstream_affected": False}))
        self.assertIsNone(sb.eligible({"statement_unchanged": "yes", "downstream_affected": False}))
        self.assertIsNone(sb.eligible(None))

    def test_parse_judgement(self):
        t = 'reasoning...\n{"statement_unchanged": true, "downstream_affected": false, "reasoning": "proof only"}'
        self.assertEqual(sb.parse_judgement(t)["reasoning"], "proof only")
        self.assertIsNone(sb.parse_judgement("no json here"))

    def test_order_new(self):
        texts = {"Sheaf/A.lean": "module\nimport Sheaf.B\n", "Sheaf/B.lean": "module\nimport Sheaf.C\n",
                 "Sheaf/C.lean": "module\nimport Mathlib\n"}
        o = sb.order_new(texts, ["Sheaf.A", "Sheaf.B", "Sheaf.C"])
        self.assertLess(o.index("Sheaf.C"), o.index("Sheaf.B"))
        self.assertLess(o.index("Sheaf.B"), o.index("Sheaf.A"))

    def test_intermediates(self):
        g = {"Sheaf.Z": {"Sheaf.Y"}, "Sheaf.Y": {"Sheaf.X", "Sheaf.W"}, "Sheaf.X": set(), "Sheaf.W": set(),
             "Sheaf.U": {"Sheaf.X"}}
        old = sb.library_graph
        sb.library_graph = lambda: g
        try:
            texts = {"Sheaf/Z.lean": "import Sheaf.Y\n", "Sheaf/X.lean": "import Mathlib\n"}
            self.assertEqual(sb.intermediates(texts, ["Sheaf.Z", "Sheaf.X"]), ["Sheaf.Y"])
            self.assertEqual(sb.intermediates({"Sheaf/Z.lean": "import Sheaf.Y\n", "Sheaf/U.lean": "import Sheaf.X\n"},
                                              ["Sheaf.Z", "Sheaf.U"]), [])
        finally:
            sb.library_graph = old

    def test_arts_of(self):
        with tempfile.TemporaryDirectory() as d:
            top = pathlib.Path(d)
            (top / "Sheaf").mkdir()
            self.assertIsNone(sb.arts_of(top, "Sheaf.A"))
            for s in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                (top / "Sheaf" / ("A" + s)).write_text("")
            a = sb.arts_of(top, "Sheaf.A")
            self.assertEqual(len(a[0]), 3)
            self.assertEqual(len(a[1]), 2)
            self.assertEqual(list(sb.import_arts([top], ["Sheaf.A", "Sheaf.B"])), ["Sheaf.A"])

    def test_sorry_findings(self):
        texts = {"Sheaf/A.lean": "theorem foo : True := by sorry\ntheorem bar : True := by sorry\n"}
        res = {"probe": {"Sheaf.A": {"sorry": ["foo", "bar._proof_1"], "axioms": []}}}
        f = sb.sorry_findings(res, {"Sheaf.A": ["foo"]}, texts)
        self.assertEqual(len(f), 1)
        self.assertIn("bar", f[0])
        res2 = {"probe": {"Sheaf.A": {"sorry": [], "axioms": [["foo", "Lean.ofReduceBool"]]}}}
        self.assertEqual(len(sb.sorry_findings(res2, {}, texts)), 1)

    def test_safe_rmtree_refuses_outside(self):
        with self.assertRaises(RuntimeError):
            sb.safe_rmtree(sb.ROOT / "lean")


if __name__ == "__main__":
    unittest.main()
