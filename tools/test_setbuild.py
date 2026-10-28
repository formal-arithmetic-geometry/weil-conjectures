#!/usr/bin/env python3
"""Tests of tools/setbuild.py (set builds, 2026-10-28), including the items of the 18:20 review."""
import json, os, pathlib, sys, tempfile, unittest
from unittest import mock
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
os.environ["SHEAF_SETBUILD_TEST_MODE"] = "on"
import setbuild as sb  # noqa: E402


class Sandbox(unittest.TestCase):
    """local/sets, the frozen tree's lib and the publish generation in a temporary directory."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = pathlib.Path(self.tmp.name)
        self.p = [mock.patch.object(sb, "SB", t / "sets"), mock.patch.object(sb, "RESULTS", t / "sets" / "results"),
                  mock.patch.object(sb, "JUDGE", t / "sets" / "judge"), mock.patch.object(sb, "PASSED", t / "sets" / "passed"),
                  mock.patch.object(sb, "NEWLINK", t / "sets" / "_new"), mock.patch.object(sb, "PUBLIB", t / "pub"),
                  mock.patch.object(sb, "GEN", t / "publish-gen"), mock.patch.object(sb, "LOG", t / "setbuild.log"),
                  mock.patch.object(sb, "published", lambda: {"commit": "c0ffee00" * 5, "time": "T"})]
        for x in self.p:
            x.start()
        (t / "sets").mkdir()
        (t / "pub" / "Sheaf").mkdir(parents=True)
        self.t = t

    def tearDown(self):
        for x in self.p:
            x.stop()
        self.tmp.cleanup()


class Pure(unittest.TestCase):
    def test_texts_sha(self):
        a = sb.texts_sha({"Sheaf/A.lean": "x", "Sheaf/B.lean": None})
        self.assertEqual(a, sb.texts_sha({"Sheaf/B.lean": None, "Sheaf/A.lean": "x"}))
        self.assertNotEqual(a, sb.texts_sha({"Sheaf/A.lean": "x", "Sheaf/B.lean": ""}))

    def test_eligible_never_defaults_to_unchanged(self):
        self.assertTrue(sb.eligible({"statement_unchanged": True, "downstream_affected": False}))
        self.assertFalse(sb.eligible({"statement_unchanged": True, "downstream_affected": True}))
        self.assertFalse(sb.eligible({"statement_unchanged": False, "downstream_affected": False}))
        self.assertIsNone(sb.eligible({"statement_unchanged": "yes", "downstream_affected": False}))
        self.assertIsNone(sb.eligible({}))
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
        with mock.patch.object(sb, "library_graph", lambda: g):
            texts = {"Sheaf/Z.lean": "import Sheaf.Y\n", "Sheaf/X.lean": "import Mathlib\n"}
            self.assertEqual(sb.intermediates(texts, ["Sheaf.Z", "Sheaf.X"]), ["Sheaf.Y"])
            self.assertEqual(sb.intermediates({"Sheaf/Z.lean": "import Sheaf.Y\n", "Sheaf/U.lean": "import Sheaf.X\n"},
                                              ["Sheaf.Z", "Sheaf.U"]), [])

    def test_arts_of(self):
        with tempfile.TemporaryDirectory() as d:
            top = pathlib.Path(d)
            (top / "Sheaf").mkdir()
            self.assertIsNone(sb.arts_of(top, "Sheaf.A"))
            for s in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                (top / "Sheaf" / ("A" + s)).write_text("")
            a = sb.arts_of(top, "Sheaf.A")
            self.assertEqual((len(a[0]), len(a[1])), (3, 2))
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

    # review item 11
    def test_exit_and_declared_missing(self):
        self.assertTrue(sb.has_exit("theorem a : True := trivial\n#exit\ntheorem b : True := trivial\n"))
        self.assertFalse(sb.has_exit("-- #exit\n/- #exit -/\ntheorem a : True := trivial\n"))
        text = "namespace X\ntheorem a : True := trivial\ntheorem b : True := trivial\nend X\n"
        self.assertEqual(sb.declared_missing(text, ["X.a", "X.b"]), [])
        self.assertEqual(sb.declared_missing(text, ["X.a"]), ["X.b"])

    # review item 13
    def test_switch_is_the_mode_file(self):
        with mock.patch.dict(os.environ, {"SHEAF_SETBUILD_TEST_MODE": ""}):
            with tempfile.TemporaryDirectory() as d, mock.patch.object(sb, "SB", pathlib.Path(d)):
                self.assertEqual(sb.mode(), "off")
                (pathlib.Path(d) / "MODE").write_text("shadow\n")
                self.assertEqual(sb.mode(), "shadow")
                with mock.patch.dict(os.environ, {"SHEAF_SETBUILD": "on"}):
                    self.assertEqual(sb.mode(), "shadow")     # the old variable no longer switches


class LakeFaithful(unittest.TestCase):
    def test_options_and_module_header(self):
        o = sb.lake_options("Sheaf.Foo")
        self.assertIs(o.get("autoImplicit"), False)              # the Sheaf library's own option
        self.assertIn("maxSynthPendingDepth", o)                  # the package's [leanOptions]
        self.assertIn("pp.unicode.fun", o)                        # dotted names, not nested tables
        self.assertNotIn("autoImplicit", sb.lake_options("WeilConjectures.Foo"))
        self.assertTrue(sb.is_module_file("/- c -/\n-- x\nmodule\n\npublic import Mathlib\n"))
        self.assertFalse(sb.is_module_file("import Mathlib\nmodule_thing\n"))
        j = json.loads(sb.setup_json("Sheaf.Foo", True, {}))
        self.assertEqual((j["isModule"], j["package"]), (True, sb.lake_package()))


class Version(Sandbox):
    # review item 6
    def test_publish_generation(self):
        self.assertEqual(sb.pub_gen(), (0, "done"))
        sb.GEN.write_text("4 done\n")
        v = sb.frozen_version(wait=0)
        self.assertEqual(v["gen"], 4)
        self.assertTrue(sb.same_version(v))
        sb.GEN.write_text("5 publishing\n")
        self.assertIsNone(sb.frozen_version(wait=0))
        self.assertFalse(sb.same_version(v))
        sb.GEN.write_text("5 done\n")
        self.assertFalse(sb.same_version(v))

    def test_no_commit_no_version(self):
        with mock.patch.object(sb, "published", lambda: {}):
            self.assertIsNone(sb.frozen_version(wait=0))


class BuildSet(Sandbox):
    """build_set with compile_one and the probe mocked: the logic of rules 3-4, items 2, 4 and 7."""
    def fake_compile(self, behaviour):
        calls = []

        def compile_one(folder, module, outdir, arts, name=None, root="src"):
            calls.append((module, sorted(arts), name))
            rc = behaviour(module, set(arts), name)
            if outdir is not None and rc == 0:
                o = (outdir / module.replace(".", "/")).with_suffix(".olean")
                o.parent.mkdir(parents=True, exist_ok=True)
                o.write_text("x")
            return {"rc": rc, "secs": 1.0, "out": "", "errors": [] if rc == 0 else ["error"], "slow": False}
        return compile_one, calls

    def run_set(self, texts, behaviour, graph=None, frozen=()):
        for m in frozen:
            p = (sb.PUBLIB / m.replace(".", "/")).with_suffix(".olean")
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("frozen")
        sb.GEN.write_text("1 done")
        v = sb.frozen_version(wait=0)
        co, calls = self.fake_compile(behaviour)
        probe = lambda folder, mods, arts: ({m: {"probed": True, "sorry": [], "axioms": [], "consts": []} for m in mods}, "")
        with mock.patch.object(sb, "compile_one", co), mock.patch.object(sb, "run_probe", probe), \
                mock.patch.object(sb, "library_graph", lambda: graph or {}), \
                mock.patch.object(sb, "shutil", mock.MagicMock()), \
                mock.patch.object(sb, "compile_intermediates", lambda *a: True):
            r = sb.build_set("G", "Sheaf.Z", "h" * 40, texts, {}, v)
        return r, calls

    def test_changed_modules_compile_against_frozen_only(self):
        texts = {"Sheaf/X.lean": "module\n", "Sheaf/Z.lean": "module\nimport Sheaf.X\n", "Sheaf/N.lean": "module\n"}
        r, calls = self.run_set(texts, lambda m, arts, name: 0, frozen=("Sheaf.X", "Sheaf.Z"))
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["new_modules"], ["Sheaf.N"])
        for module, arts, name in calls:
            self.assertTrue(set(arts) <= {"Sheaf.N"}, (module, arts))     # never X' for Z, never another set's module

    def test_compiles_only_with_primed_versions_is_interface_change(self):
        texts = {"Sheaf/X.lean": "module\n", "Sheaf/Z.lean": "module\nimport Sheaf.X\n"}
        beh = lambda m, arts, name: 0 if (m != "Sheaf.Z" or "Sheaf.X" in arts) else 1
        r, _ = self.run_set(texts, beh, graph={"Sheaf.Z": {"Sheaf.X"}, "Sheaf.X": set()}, frozen=("Sheaf.X", "Sheaf.Z"))
        self.assertFalse(r["ok"])
        self.assertEqual(r["phase"], "interface-changed")

    def test_through_intermediates_is_interface_change_too(self):
        texts = {"Sheaf/X.lean": "module\n", "Sheaf/Z.lean": "module\nimport Sheaf.Y\n"}
        g = {"Sheaf.Z": {"Sheaf.Y"}, "Sheaf.Y": {"Sheaf.X"}, "Sheaf.X": set()}
        beh = lambda m, arts, name: 0 if (m != "Sheaf.Z" or "Sheaf.X" in arts) else 1
        r, _ = self.run_set(texts, beh, graph=g, frozen=("Sheaf.X", "Sheaf.Z", "Sheaf.Y"))
        self.assertEqual(r["intermediates"], ["Sheaf.Y"])
        self.assertEqual(r["phase"], "interface-changed")
        self.assertFalse(r["ok"])

    def test_plain_failure_is_compile(self):
        texts = {"Sheaf/X.lean": "module\n", "Sheaf/Z.lean": "module\n"}
        r, _ = self.run_set(texts, lambda m, arts, name: 1 if m == "Sheaf.Z" else 0, frozen=("Sheaf.X", "Sheaf.Z"))
        self.assertEqual(r["phase"], "compile")

    def test_complete_folder_is_never_rebuilt(self):
        texts = {"Sheaf/X.lean": "module\n"}
        r1, calls1 = self.run_set(texts, lambda m, arts, name: 0, frozen=("Sheaf.X",))
        r2, calls2 = self.run_set(texts, lambda m, arts, name: 1, frozen=("Sheaf.X",))
        self.assertTrue(r2["ok"])
        self.assertEqual(calls2, [])
        self.assertEqual(r1["id"], r2["id"])

    def test_probe_requires_the_sets_own_files(self):
        texts = {"Sheaf/X.lean": "module\n"}

        def co(folder, module, outdir, arts, name=None, root="src"):
            return {"rc": 0, "secs": 1.0, "out": "", "errors": [], "slow": False}   # writes no .olean
        sb.GEN.write_text("1 done")
        v = sb.frozen_version(wait=0)
        p = (sb.PUBLIB / "Sheaf/X.olean"); p.write_text("f")
        with mock.patch.object(sb, "compile_one", co), mock.patch.object(sb, "shutil", mock.MagicMock()):
            r = sb.build_set("G", "Sheaf.X", "a" * 40, texts, {}, v)
        self.assertEqual(r["phase"], "probe")

    def test_republished_during_build_is_infra(self):
        texts = {"Sheaf/X.lean": "module\n"}
        sb.GEN.write_text("1 done")
        v = sb.frozen_version(wait=0)
        (sb.PUBLIB / "Sheaf/X.olean").write_text("f")

        def co(folder, module, outdir, arts, name=None, root="src"):
            sb.GEN.write_text("2 publishing")
            return {"rc": 1, "secs": 1.0, "out": "", "errors": ["e"], "slow": False}
        with mock.patch.object(sb, "compile_one", co), mock.patch.object(sb, "shutil", mock.MagicMock()):
            r = sb.build_set("G", "Sheaf.X", "b" * 40, texts, {}, v)
        self.assertEqual(r["phase"], "infra")


class Passes(Sandbox):
    """Review items 1, 5, 8, 9: a pass holds only while everything it rests on holds."""
    def setUp(self):
        super().setUp()
        self.head = "d" * 40
        self.rec = {"id": "s", "folder": str(self.t / "sets" / "s"), "group": "G", "item": "Sheaf.A", "head": self.head,
                    "sha": "S1", "modules": ["Sheaf.A"], "new_modules": [], "changed_modules": ["Sheaf.A"]}
        sb.write_json(sb.RESULTS / f"{self.head}.json", {"ok": True, "sha": "S1", "head": self.head})
        sb.write_json(sb.JUDGE / f"{self.head}__S1.json", {"statement_unchanged": True, "downstream_affected": False})
        self.bh = mock.patch.object(sb, "branch_head", lambda g, i: self.head)
        self.vd = mock.patch.object(sb, "verdict_of", lambda h: {})
        self.bh.start(); self.vd.start()

    def tearDown(self):
        self.bh.stop(); self.vd.stop()
        super().tearDown()

    def test_valid(self):
        self.assertIsNone(sb.valid_pass(self.rec))

    def test_return_revokes(self):
        with mock.patch.object(sb, "verdict_of", lambda h: {"verdict": "RETURN"}):
            self.assertIn("returned", sb.valid_pass(self.rec))

    def test_moved_head(self):
        with mock.patch.object(sb, "branch_head", lambda g, i: "e" * 40):
            self.assertIn("moved", sb.valid_pass(self.rec))

    def test_failed_latest_or_other_texts(self):
        sb.write_json(sb.RESULTS / f"{self.head}.json", {"ok": False, "sha": "S1"})
        self.assertIsNotNone(sb.valid_pass(self.rec))
        sb.write_json(sb.RESULTS / f"{self.head}.json", {"ok": True, "sha": "S2"})
        self.assertIsNotNone(sb.valid_pass(self.rec))

    def test_judgement_keyed_by_texts(self):
        self.assertIsNotNone(sb.judgement(self.head, "S1"))
        self.assertIsNone(sb.judgement(self.head, "S2"))

    def test_record_marks_done_with_set_sources_and_rolls_back(self):
        r = dict(self.rec)
        seen = []

        def run(cmd, **kw):
            seen.append(cmd)
            return mock.Mock(returncode=1, stdout="", stderr="boom")
        with mock.patch.object(sb.subprocess, "run", run), mock.patch.object(sb, "refresh_newlib", lambda: None):
            why = sb.record_passed(r)
        self.assertIn("queue_mark failed", why)
        self.assertIn("--source-dir", seen[0])
        self.assertFalse((sb.PASSED / f"{self.head}.json").exists())
        with mock.patch.object(sb.subprocess, "run", lambda cmd, **kw: mock.Mock(returncode=0, stdout="", stderr="")), \
                mock.patch.object(sb, "refresh_newlib", lambda: None):
            self.assertIsNone(sb.record_passed(r))
        self.assertTrue((sb.PASSED / f"{self.head}.json").exists())

    def test_two_passed_sets_on_one_module(self):
        other = dict(self.rec, head="f" * 40, group="H", item="Sheaf.B")
        sb.write_json(sb.PASSED / f"{'f' * 40}.json", other)
        sb.write_json(sb.RESULTS / f"{'f' * 40}.json", {"ok": True, "sha": "S1"})
        sb.write_json(sb.JUDGE / f"{'f' * 40}__S1.json", {"statement_unchanged": True, "downstream_affected": False})
        with mock.patch.object(sb, "branch_head", lambda g, i: "f" * 40 if g == "H" else self.head):
            why = sb.record_passed(dict(self.rec))
        self.assertIn("does not pass", why)

    def test_landed_with_other_texts_revokes(self):
        sb.write_json(sb.PASSED / f"{self.head}.json", dict(self.rec, sha=sb.texts_sha({"Sheaf/A.lean": "x"})))
        with mock.patch.object(sb.subprocess, "run", lambda *a, **k: mock.Mock(returncode=0)), \
                mock.patch.object(sb, "refresh_newlib", lambda: None):
            sb.landed_text_check(self.head, {"Sheaf/A.lean": "x"})
            self.assertTrue((sb.PASSED / f"{self.head}.json").exists())
            sb.landed_text_check(self.head, {"Sheaf/A.lean": "y"})
            self.assertFalse((sb.PASSED / f"{self.head}.json").exists())

    def test_landed_head_is_retired_not_reworked(self):
        sb.write_json(sb.PASSED / f"{self.head}.json", self.rec)
        calls = []
        with mock.patch.object(sb, "outcome", lambda h: {"state": "landed", "batch": "B", "landing": "L"}), \
                mock.patch.object(sb.subprocess, "run", lambda *a, **k: calls.append(a) or mock.Mock(returncode=0)):
            sb.retire_or_revoke(self.rec, "the branch head moved")
        self.assertFalse((sb.PASSED / f"{self.head}.json").exists())
        self.assertEqual(calls, [])                                  # no queue_mark rework
        sb.write_json(sb.PASSED / f"{self.head}.json", self.rec)
        with mock.patch.object(sb, "outcome", lambda h: None), mock.patch.object(sb, "refresh_newlib", lambda: None), \
                mock.patch.object(sb.subprocess, "run", lambda *a, **k: calls.append(a) or mock.Mock(returncode=0)):
            sb.retire_or_revoke(self.rec, "the branch head moved")
        self.assertEqual(len(calls), 1)                              # returned/replaced: rework

    def test_is_passed_never_for_returned(self):
        sb.write_json(sb.PASSED / f"{self.head}.json", self.rec)
        self.assertTrue(sb.is_passed("G", "Sheaf.A", self.head))
        with mock.patch.object(sb, "verdict_of", lambda h: {"verdict": "RETURN"}):
            self.assertFalse(sb.is_passed("G", "Sheaf.A", self.head))


class Gates(unittest.TestCase):
    # review item 3
    def dv(self, text, role="item", old="module\n"):
        return {"D": {"fails": [], "modules": [{"file": "lean/Sheaf/A.lean", "module": "Sheaf.A", "role": role,
                                                 "old": old, "text": text}]},
                "roles": [role], "texts": {"Sheaf/A.lean": text}}

    def test_exit_refused(self):
        with mock.patch.object(sb, "library_graph", lambda: {}):
            r = sb.gates(self.dv("module\ntheorem a : True := trivial\n#exit\n"), {"commit": "HEAD"})
        self.assertEqual(r[0], "static")

    def test_delete_not_eligible(self):
        r = sb.gates(self.dv(None), {"commit": "HEAD"})
        self.assertEqual(r[0], "not-eligible")

    def test_missing_import_waits(self):
        with mock.patch.object(sb, "library_graph", lambda: {}):
            r = sb.gates(self.dv("module\nimport Sheaf.DoesNotExistAnywhere\ntheorem a : True := trivial\n"), {"commit": "HEAD"})
        self.assertEqual(r[0], "wait-dependency")


if __name__ == "__main__":
    unittest.main()
