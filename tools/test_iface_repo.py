#!/usr/bin/env python3
"""Tests of tools/iface_repo.py (unittest; python3 tools/test_iface_repo.py). Everything runs in temporary git
repositories; nothing reads or writes the live repository."""
import json, os, pathlib, subprocess, sys, tempfile, unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import iface_repo as ir  # noqa: E402


def sh(cwd, *a):
    r = subprocess.run(a, cwd=cwd, capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f"{a}: {r.stderr}")
    return r.stdout


def commit_all(repo, msg):
    sh(repo, "git", "add", "-A")
    sh(repo, "git", "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", msg)
    return sh(repo, "git", "rev-parse", "HEAD").strip()


LEAN_A = """module

public import Mathlib.Logic.Basic

namespace Sheaf

theorem foo : 1 = 1 := by
  rfl

theorem bar (n : Nat) : n = n := by
  sorry

end Sheaf
"""


class Env:
    """A fake live repository and interface home, wired into the module's globals."""

    def __init__(self):
        self.t = tempfile.TemporaryDirectory()
        base = pathlib.Path(self.t.name)
        self.live = base / "live"
        (self.live / "lean" / "Sheaf").mkdir(parents=True)
        (self.live / "dag" / "nodes").mkdir(parents=True)
        (self.live / "coord" / "claims").mkdir(parents=True)
        sh(self.live, "git", "init", "-q", "-b", "sheaf-dag")
        (self.live / "lean" / "Sheaf" / "A.lean").write_text(LEAN_A)
        (self.live / "lean" / "Sheaf" / "B.lean").write_text("module\n\npublic import Sheaf.A\n\ntheorem baz : True := trivial\n")
        (self.live / "dag" / "nodes" / "n-a.json").write_text(json.dumps({"id": "n-a", "statement": "old", "lean": {"module": "Sheaf.A", "decl": "Sheaf.foo"}}))
        (self.live / "dag" / "nodes" / "n-b.json").write_text(json.dumps({"id": "n-b", "statement": "b", "stmt_deps": ["n-a"], "lean": {"module": "Sheaf.B"}}))
        (self.live / ".gitignore").write_text("local/\ncoord/claims/\n")
        self.base = commit_all(self.live, "base")
        self.saved = {k: getattr(ir, k) for k in ("ROOT", "HOME", "REPO", "RLEAN", "ST", "ITEMS", "BUILDS", "ERRS", "LOGF", "PUB", "FIX_DIR", "ensure_lake")}
        ir.ROOT = self.live
        ir.HOME = base / "iface"
        ir.REPO = ir.HOME / "repo"
        ir.RLEAN = ir.REPO / "lean"
        ir.ST = self.live / "local" / "iface"
        ir.ITEMS = ir.ST / "items"
        ir.BUILDS = ir.ST / "builds"
        ir.ERRS = ir.HOME / "build-errors"
        ir.LOGF = ir.ST / "iface.log"
        ir.PUB = self.live / "local" / "builds" / "published.json"
        ir.FIX_DIR = self.live / "local" / "verdicts" / "3"
        ir.ensure_lake = lambda: None
        ir.PUB.parent.mkdir(parents=True)
        ir.PUB.write_text(json.dumps({"commit": self.base, "time": "2026-10-28T00:00:00Z",
                                      "source_fingerprint": "x|targets:Sheaf,TargetsCheck"}))
        os.environ["SHEAF_IFACE"] = "shadow"

    def deliver(self, g, item, edits, claim=True):
        sh(self.live, "git", "checkout", "-q", "-b", f"deliver/{g}/{item}", self.base)
        for rel, text in edits.items():
            p = self.live / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        h = commit_all(self.live, f"deliver {item}")
        sh(self.live, "git", "checkout", "-q", "sheaf-dag")
        if claim:
            (self.live / "coord" / "claims" / f"{item}.lock").write_text(json.dumps({"who": g}))
        return h

    def close(self):
        for k, v in self.saved.items():
            setattr(ir, k, v)
        os.environ.pop("SHEAF_IFACE", None)
        self.t.cleanup()


class Routing(unittest.TestCase):
    def test_judgement(self):
        j = lambda su, da: {"phase": "not-eligible", "judgement": {"statement_unchanged": su, "downstream_affected": da, "source": "reviewer"}}
        self.assertIsNone(ir.judged_statement_changing(j(True, False)))
        self.assertIn("statements/interface change", ir.judged_statement_changing(j(False, False)))
        self.assertIn("downstream affected", ir.judged_statement_changing(j(True, True)))
        self.assertIsNotNone(ir.judged_statement_changing({"phase": "interface-changed", "why": "x"}))
        self.assertIsNone(ir.judged_statement_changing({"phase": "built", "ok": True}))
        self.assertIsNone(ir.judged_statement_changing({"phase": "not-eligible", "why": "roles node"}))   # no judgement: not routed
        self.assertIsNotNone(ir.judged_statement_changing({"phase": "not-eligible", "why": "the delivery deletes a module"}))
        self.assertIsNone(ir.judged_statement_changing({"phase": "not-eligible", "judgement": {"statement_unchanged": "?"}}))

    def test_module_of(self):
        self.assertEqual(ir.module_of("lean/Sheaf/A/B.lean"), "Sheaf.A.B")


class Repository(unittest.TestCase):
    def setUp(self):
        self.e = Env()

    def tearDown(self):
        self.e.close()

    def test_route_apply_pause(self):
        e = self.e
        new_a = LEAN_A.replace("theorem foo : 1 = 1", "theorem foo : 2 = 2")
        node = json.dumps({"id": "n-a", "statement": "new", "lean": {"module": "Sheaf.A", "decl": "Sheaf.foo"}})
        h = e.deliver("G1", "Sheaf.A", {"lean/Sheaf/A.lean": new_a, "dag/nodes/n-a.json": node,
                                         "coord/changes/x.md": "# x\n\n## Status\nopen\n"})
        ir.init()
        self.assertTrue((ir.REPO / "lean" / "Sheaf" / "A.lean").is_file())
        rs = ir.intake(add=("G1", "Sheaf.A", None))
        self.assertEqual(len(rs), 1)
        r = rs[0]
        self.assertEqual(r["modules"], ["Sheaf.A"])
        self.assertEqual(r["nodes"], ["n-a"])
        self.assertEqual(ir.intake(add=("G1", "Sheaf.A", None)), [])        # same head: nothing new
        self.assertFalse(ir.routed_head("G1", "Sheaf.A", h))                 # shadow: the lander is not told
        os.environ["SHEAF_IFACE"] = "on"
        self.assertTrue(ir.routed_head("G1", "Sheaf.A", h))
        self.assertFalse(ir.routed_head("G1", "Sheaf.A", "0" * 40))
        os.environ["SHEAF_IFACE"] = "shadow"
        res = ir.apply_all()
        self.assertEqual(res, {"G1__Sheaf.A": "applied"})
        self.assertIn("2 = 2", (ir.REPO / "lean" / "Sheaf" / "A.lean").read_text())
        self.assertIn("applied in the interface repository", (ir.REPO / "coord" / "changes" / "x.md").read_text())
        self.assertNotIn("2 = 2", (e.live / "lean" / "Sheaf" / "A.lean").read_text())   # main untouched
        it = ir.read_json(ir.item_path("G1", "Sheaf.A"))
        self.assertEqual(it["state"], "applied")
        seeds = ir.pause_seeds()
        self.assertIn("Sheaf.A", seeds["modules"])
        self.assertIn("n-a", seeds["nodes"])

        class G:
            live = {"n-a": {"id": "n-a", "lean": {"module": "Sheaf.A"}}, "n-b": {"id": "n-b", "stmt_deps": ["n-a"], "lean": {"module": "Sheaf.B"}},
                    "n-c": {"id": "n-c", "lean": {"module": "Sheaf.C"}}}

            def deps(self, j, which):
                return self.live[j].get("stmt_deps") or []
        import types
        sys.modules.setdefault("dag_queue", types.SimpleNamespace(module_of=lambda d: (d.get("lean") or {}).get("module")))
        self.assertEqual(ir.paused_sets(G(), seeds), (set(), set(), {}))      # shadow: nothing paused
        os.environ["SHEAF_IFACE"] = "on"
        nodes, mods, why = ir.paused_sets(G(), seeds)
        self.assertEqual(nodes, {"n-b"})
        self.assertEqual(mods, {"Sheaf.A", "Sheaf.B"})
        self.assertNotIn("Sheaf.C", mods)

    def test_conflict_and_resolution(self):
        e = self.e
        h1 = e.deliver("G1", "Sheaf.A", {"lean/Sheaf/A.lean": LEAN_A.replace("1 = 1", "2 = 2")})
        h2 = e.deliver("G2", "Sheaf.B", {"lean/Sheaf/A.lean": LEAN_A.replace("1 = 1", "3 = 3")})
        ir.init()
        ir.intake(add=("G1", "Sheaf.A", None)); ir.intake(add=("G2", "Sheaf.B", None))
        res = ir.apply_all()
        self.assertEqual(res.get("G1__Sheaf.A"), "applied")
        self.assertEqual(res.get("G2__Sheaf.B"), "conflict")
        it = ir.read_json(ir.item_path("G2", "Sheaf.B"))
        self.assertEqual(it["state"], "conflict")
        self.assertEqual(ir.dirty(), [])                                    # the conflict was put back; others apply
        self.assertEqual(ir.main(["reapply", "G2", "Sheaf.B"]), 0)          # the agent asks for the markers
        self.assertIn("<<<<<<<", (ir.REPO / "lean" / "Sheaf" / "A.lean").read_text())
        self.assertIn("waiting", ir.apply_all())                            # nothing applied over the agent's work
        # the agent resolves and commits
        (ir.REPO / "lean" / "Sheaf" / "A.lean").write_text(LEAN_A.replace("1 = 1", "3 = 3"))
        sh(ir.REPO, "git", "add", "-A")
        sh(ir.REPO, "git", "commit", "-q", "-m", "resolve")
        self.assertEqual(ir.main(["applied", "G2", "Sheaf.B"]), 0)
        self.assertEqual(ir.read_json(ir.item_path("G2", "Sheaf.B"))["state"], "applied")

    def test_new_head_of_applied_item(self):
        e = self.e
        e.deliver("G1", "Sheaf.A", {"lean/Sheaf/A.lean": LEAN_A.replace("1 = 1", "2 = 2")})
        ir.init(); ir.intake(add=("G1", "Sheaf.A", None)); ir.apply_all()
        # the writer pushes a second commit on the branch
        sh(e.live, "git", "checkout", "-q", "deliver/G1/Sheaf.A")
        (e.live / "lean" / "Sheaf" / "A.lean").write_text(LEAN_A.replace("1 = 1", "2 = 2").replace("theorem baz", "theorem baz2"))
        (e.live / "lean" / "Sheaf" / "A.lean").write_text(LEAN_A.replace("1 = 1", "2 = 2") + "\ntheorem extra : True := trivial\n")
        commit_all(e.live, "more")
        sh(e.live, "git", "checkout", "-q", "sheaf-dag")
        rs = ir.intake(add=("G1", "Sheaf.A", None))
        self.assertEqual(rs[0]["state"], "queued")
        self.assertTrue(rs[0]["prev_applied"])
        self.assertEqual(ir.apply_all(), {"G1__Sheaf.A": "applied"})
        self.assertIn("theorem extra", (ir.REPO / "lean" / "Sheaf" / "A.lean").read_text())

    def test_sorry_regression_and_merge_due(self):
        e = self.e
        ir.init()
        base = sh(ir.REPO, "git", "rev-parse", "HEAD").strip()
        p = ir.REPO / "lean" / "Sheaf" / "A.lean"
        p.write_text(LEAN_A.replace("theorem foo : 1 = 1 := by\n  rfl", "theorem foo : 1 = 1 := by\n  sorry").replace("theorem bar (n : Nat) : n = n := by\n  sorry", ""))
        head = commit_all(ir.REPO, "agent sorried foo")
        regress, removed = ir.sorry_regressions(base, head)
        self.assertTrue(any("foo" in x for x in regress), regress)
        self.assertTrue(any("bar" in x for x in removed), removed)
        # merge_due: nothing applied
        self.assertIsNone(ir.merge_due()[0])
        r = {"group": "G1", "item": "Sheaf.A", "head": head, "state": "green", "applied_commit": head, "routed": ir.now()}
        ir.save_item(r)
        s = ir.state(); s["last_green"] = {"commit": head}; s["last_build"] = {"commit": head, "result": "green"}; ir.save_state(s)
        c, why = ir.merge_due()
        self.assertEqual(c, head, why)
        # an open item keeps it from merging until the age limit
        ir.save_item({"group": "G2", "item": "Sheaf.B", "head": head, "state": "applied", "applied_commit": head, "routed": ir.now()})
        self.assertIsNone(ir.merge_due()[0])
        s = ir.state(); s["first_applied"] = "2026-01-01T00:00:00Z"; ir.save_state(s)
        c, why = ir.merge_due()
        self.assertEqual(c, head)
        self.assertIn("older than", why)

    def test_merge_prepare_and_land_refused_in_shadow(self):
        e = self.e
        e.deliver("G1", "Sheaf.A", {"lean/Sheaf/A.lean": LEAN_A.replace("1 = 1", "2 = 2")})
        ir.init(); ir.intake(add=("G1", "Sheaf.A", None)); ir.apply_all()
        tip = sh(ir.REPO, "git", "rev-parse", "HEAD").strip()
        ir.mark_green(tip)
        self.assertEqual(ir.read_json(ir.item_path("G1", "Sheaf.A"))["state"], "green")
        # main moves meanwhile (a proof-only landing)
        (e.live / "lean" / "Sheaf" / "B.lean").write_text("module\n\npublic import Sheaf.A\n\ntheorem baz : True := by trivial\n")
        commit_all(e.live, "proof in main")
        st = ir.merge_prepare(tip)
        self.assertEqual(st["phase"], "prepared", st)
        self.assertEqual(ir.read_json(ir.item_path("G1", "Sheaf.A"))["state"], "merging")
        txt = (ir.REPO / "lean" / "Sheaf" / "B.lean").read_text()
        self.assertIn("by trivial", txt)                                     # main's change is in the candidate
        self.assertIn("2 = 2", (ir.REPO / "lean" / "Sheaf" / "A.lean").read_text())
        self.assertEqual(ir.merge_land()["result"], "refused")               # shadow
        self.assertNotIn("2 = 2", (e.live / "lean" / "Sheaf" / "A.lean").read_text())

    def test_fix_files(self):
        e = self.e
        head = "a" * 40
        fx = ir.FIX_DIR / head / "fixes"
        fx.mkdir(parents=True)
        (ir.FIX_DIR / f"{head}.json").write_text(json.dumps({"verdict": "FIX"}))
        (fx / "A.lean").write_text("fixed")
        (fx / "Sheaf.A.report.md").write_text("rep")
        (fx / "chg.change.md").write_text("chg")
        out = ir.fix_files("G1", "Sheaf.A", head, ["lean/Sheaf/A.lean", "dag/nodes/n-a.json"])
        self.assertEqual(out["lean/Sheaf/A.lean"], "fixed")
        self.assertEqual(out["coord/reports/G1/Sheaf.A.md"], "rep")
        self.assertEqual(out["coord/changes/chg.md"], "chg")
        (ir.FIX_DIR / f"{head}.json").write_text(json.dumps({"verdict": "PASS"}))
        self.assertEqual(ir.fix_files("G1", "Sheaf.A", head, ["lean/Sheaf/A.lean"]), {})

    def test_targets(self):
        self.assertEqual(ir.targets(), ["Sheaf", "TargetsCheck"])


if __name__ == "__main__":
    unittest.main()
