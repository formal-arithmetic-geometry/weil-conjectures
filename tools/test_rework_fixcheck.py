"""tools/rework_fixcheck.py: a rework root fix lands only when it differs from the failing quarantined text and
compiles alone (compiler faked). Run: python3 tools/test_rework_fixcheck.py"""
import pathlib, sys, tempfile, unittest
from unittest.mock import patch
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import rework_fixcheck as rfc


class Refuse(Exception): pass
class Wait(Exception): pass


ROOT_MOD = "Sheaf.Fixture.RootFixCheckRoot"
DEP_MOD = "Sheaf.Fixture.RootFixCheckDep"
BAD = "module\npublic import Mathlib\npublic theorem t : True := by exact False.elim\n"
GOOD = "module\npublic import Mathlib\npublic theorem t : True := trivial\n"
CAUSE = "error: Sheaf/Fixture/RootFixCheckRoot.lean:3:2: Type mismatch"


def rows(cause=CAUSE):
    return {ROOT_MOD: {"module": ROOT_MOD, "quarantine": "quarantine/none/RootFixCheckRoot.lean", "cause": cause},
            DEP_MOD: {"module": DEP_MOD, "quarantine": "quarantine/none/RootFixCheckDep.lean", "cause": "imports X"}}


def delivery(text, extra=()):
    return {"modules": [{"module": ROOT_MOD, "role": "item", "old": BAD, "text": text}, *extra]}


class FixCheck(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        p = [patch.object(rfc, "STATE", pathlib.Path(self.tmp.name)), patch.object(rfc, "tried", return_value={}),
             patch.object(rfc, "_published", return_value="pub1")]
        for x in p:
            x.start(); self.addCleanup(x.stop)
        self.addCleanup(self.tmp.cleanup)
        self.compiled = []

    def fake(self, res, out=""):
        def f(mod, text):
            self.compiled.append(mod); return res, out
        return f

    def verify(self, D, res="ok", out="", **kw):
        return rfc.verify(D, ROOT_MOD, "h" * 40, Refuse, Wait, rows=kw.pop("rows", rows()), compile_fn=self.fake(res, out), **kw)

    def test_unchanged_failing_text_refused_without_compile(self):
        with self.assertRaises(Refuse) as e:
            self.verify(delivery(BAD))
        self.assertIn("AUTO review does not apply", str(e.exception))
        self.assertIn("Type mismatch", str(e.exception))
        self.assertEqual(self.compiled, [])

    def test_whitespace_only_change_is_unchanged(self):
        with self.assertRaises(Refuse):
            self.verify(delivery(BAD.replace("False.elim", "False.elim   ") + "\n\n"))

    def test_tried_blob_refused_even_without_error_cause(self):
        with patch.object(rfc, "tried", return_value={ROOT_MOD: rfc.sha1(BAD)}):
            with self.assertRaises(Refuse):
                self.verify(delivery(BAD), rows=rows(cause="imports gone module"))

    def test_verbatim_restore_of_non_error_root_is_compiled_not_refused(self):
        self.assertEqual(self.verify(delivery(BAD), rows=rows(cause="imports gone module")), {ROOT_MOD: "compiled"})

    def test_changed_text_that_fails_to_compile_refused(self):
        with self.assertRaises(Refuse) as e:
            self.verify(delivery(GOOD), res="error", out="x.lean:3:2: error: unknown identifier\nmore")
        self.assertIn("unknown identifier", str(e.exception))

    def test_changed_text_that_compiles_lands_and_is_cached(self):
        self.assertEqual(self.verify(delivery(GOOD)), {ROOT_MOD: "compiled"})
        self.assertEqual(self.verify(delivery(GOOD), res="error"), {ROOT_MOD: "compiled"})
        self.assertEqual(self.compiled, [ROOT_MOD])

    def test_missing_olean_waits_then_lands_after_the_limit(self):
        with self.assertRaises(Wait):
            self.verify(delivery(GOOD), res="missing", out="error: object file x of module Y does not exist")
        with patch.dict("os.environ", {"SHEAF_ROOTFIX_WAIT": "0"}):
            st = self.verify(delivery(GOOD), res="missing")
        self.assertIn("wait limit", st[ROOT_MOD])

    def test_root_importing_restored_quarantined_module_not_compiled_alone(self):
        dep = {"module": DEP_MOD, "role": "restored", "old": "module\n", "text": "module\n"}
        text = GOOD.replace("public import Mathlib", f"public import Mathlib\npublic import {DEP_MOD}")
        self.assertEqual(self.verify(delivery(text, [dep])), {ROOT_MOD: "with its restored imports"})
        self.assertEqual(self.compiled, [])

    def test_reader_pass_does_not_compile(self):
        self.assertIn("not compiled yet", self.verify(delivery(GOOD), compile=False)[ROOT_MOD])
        self.assertEqual(self.compiled, [])
        with self.assertRaises(Refuse):
            self.verify(delivery(BAD), compile=False)

    def test_delivery_without_rework_root_untouched(self):
        D = {"modules": [{"module": "Sheaf.Fixture.Other", "role": "item", "old": BAD, "text": BAD}]}
        self.assertEqual(rfc.verify(D, "Sheaf.Fixture.Other", "h" * 40, Refuse, Wait, rows=rows(),
                                    compile_fn=self.fake("error")), {})


if __name__ == "__main__":
    unittest.main()
