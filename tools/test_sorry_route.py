"""Route refresh regressions: an unrelated failed batch cannot keep successful batches stale."""
import copy
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import sorry_route as sr


def snapshot(commit, t, batches, **extra):
    return dict(commit=commit, t=t, ok=True, batches=batches, route={}, targets={}, own={},
                own_failed=[], failed=[], **extra)


class RetentionTests(unittest.TestCase):
    def test_main_publishes_healthy_batch_despite_an_unrelated_missing_artifact(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "local").mkdir()
            old = snapshot("old", 10, {"batch2": {"Sheaf.Needed": ["needed"]},
                                       "batch5": {"Sheaf.Unused": ["unused"]}})
            (root / "local/sorry-route.json").write_text(json.dumps(old))
            import leanindex
            with patch.object(sr, "R", root), patch.object(sr, "open_batches", lambda: [2, 5]), \
                 patch.object(sr, "targets", lambda n: [f"Sheaf.Target{n}"]), \
                 patch.object(sr, "build_commit", lambda: "new"), \
                 patch.object(sr.assumed, "decls_for", lambda n: set()), \
                 patch.object(sr, "declaring", lambda m: [m]), \
                 patch.object(sr, "walk", lambda m, *args: None if m == "Sheaf.Target2" else {}), \
                 patch.object(leanindex, "scan", lambda: ({}, {})), patch.object(sys, "argv", ["sorry_route.py"]):
                self.assertEqual(sr.main(), 1)  # diagnostics still expose the failed walk
                current = json.loads((root / "local/sorry-route.json").read_text())
                self.assertTrue(current["ok"])
                self.assertEqual(current["batches"]["batch2"], old["batches"]["batch2"])
                self.assertEqual(current["batches"]["batch5"], {})
                self.assertEqual(current["batch_commits"], {"batch2": "old", "batch5": "new"})
                self.assertEqual(sr.load()["route"], {"Sheaf.Needed"})

    def test_failed_batch_keeps_whole_route_while_successful_empty_batch_updates(self):
        old = snapshot("old", 10, {"batch2": {"Sheaf.Needed": ["needed"]},
                                   "batch5": {"Sheaf.Unused": ["unused"]}})
        fresh = snapshot("new", 20, {"batch2": {"Sheaf.Partial": ["partial"]}, "batch5": {}})
        fresh["failed"] = ["Sheaf.MissingArtifact"]
        out = sr.retain_failed_batches(fresh, old, {"batch2"})
        self.assertTrue(out["ok"])
        self.assertEqual(out["retained"], ["batch2"])
        self.assertEqual(out["route"], {"Sheaf.Needed": ["needed"]})
        self.assertEqual(out["batch_commits"], {"batch2": "old", "batch5": "new"})
        self.assertEqual(out["batch_times"], {"batch2": 10, "batch5": 20})
        again = snapshot("newer", 30, {"batch2": {}, "batch5": {}})
        again = sr.retain_failed_batches(again, out, {"batch2"})
        self.assertEqual(again["batch_commits"]["batch2"], "old")
        self.assertEqual(again["batch_times"]["batch2"], 10)

    def test_failed_batch_without_a_previous_complete_walk_is_not_certified(self):
        for old in (None, dict(ok=False, batches={"batch2": {}})):
            fresh = snapshot("new", 20, {"batch2": {}, "batch5": {}})
            out = sr.retain_failed_batches(fresh, old, {"batch2"})
            self.assertFalse(out["ok"])
            self.assertEqual(out["retained"], [])

    def test_route_union_and_failed_own_reporting_are_preserved(self):
        old = snapshot("old", 10, {"batch2": {"Sheaf.Shared": ["old"]}},
                       batch_commits={"batch2": "earlier"}, batch_times={"batch2": 5})
        old["own"] = {"batch2": {"Sheaf.Own": ["own"]}}
        old["targets"] = {"Sheaf.Target2": {"Sheaf.Shared": ["old"]}}
        fresh = snapshot("new", 20, {"batch2": {}, "batch5": {"Sheaf.Shared": ["new"]}})
        fresh["failed"] = ["Sheaf.Target2"]
        fresh["own_failed"] = ["batch2:Sheaf.Target2"]
        out = sr.retain_failed_batches(fresh, old, {"batch2"})
        self.assertEqual(out["route"], {"Sheaf.Shared": ["new", "old"]})
        self.assertEqual(out["own"], old["own"])
        self.assertEqual(out["targets"], old["targets"])
        self.assertEqual(out["batch_commits"]["batch2"], "earlier")


class SourceBaselineTests(unittest.TestCase):
    def test_real_git_diff_uses_each_batchs_baseline_and_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
            git("init", "-q")
            (root / "lean/Sheaf").mkdir(parents=True)
            for name in ("Unused", "Needed", "Shared", "NewWork"):
                (root / f"lean/Sheaf/{name}.lean").write_text("-- original\n")
            git("add", "lean")
            git("-c", "user.name=Test", "-c", "user.email=test@example.com", "commit", "-qm", "old")
            old = git("rev-parse", "HEAD")
            for name in ("Unused", "Needed", "Shared"):
                (root / f"lean/Sheaf/{name}.lean").write_text("-- restored source\n")
            git("add", "lean")
            git("-c", "user.name=Test", "-c", "user.email=test@example.com", "commit", "-qm", "published")
            new = git("rev-parse", "HEAD")
            (root / "lean/Sheaf/NewWork.lean").write_text("-- split since published\n")
            (root / "lean/Sheaf/Untracked.lean").write_text("-- new dependency\n")
            d = snapshot(new, 20, {"batch2": {}, "batch5": {}},
                         batch_commits={"batch2": old, "batch5": new},
                         batch_times={"batch2": 10, "batch5": 20})
            (root / "local").mkdir()
            (root / "local/sorry-route.json").write_text(json.dumps(d))
            imports = {"Sheaf.Target2": {"Sheaf.Needed", "Sheaf.Shared"},
                       "Sheaf.Target5": {"Sheaf.Unused", "Sheaf.Shared", "Sheaf.NewWork", "Sheaf.Untracked"}}
            with patch.object(sr, "R", root), patch.object(sr, "_SNAPSHOTS", {}), \
                 patch.object(sr, "targets", lambda n: [f"Sheaf.Target{n}"]):
                route = sr.load()
                self.assertEqual(sr.changed_in_batches(route, imports),
                                 {"Sheaf.Needed", "Sheaf.Shared", "Sheaf.NewWork", "Sheaf.Untracked"})
                self.assertEqual(sr.changed_since(20, imports["Sheaf.Target5"], "batch5"),
                                 {"Sheaf.NewWork", "Sheaf.Untracked"})
                self.assertEqual(sr.changed_since(20, imports["Sheaf.Target2"], "batch2"),
                                 {"Sheaf.Needed", "Sheaf.Shared"})
                # Legacy snapshots still compare every batch to their single recorded commit.
                legacy = copy.deepcopy(d)
                legacy.pop("batch_commits")
                sr._SNAPSHOTS[20] = legacy
                self.assertEqual(sr.changed_since(20, {"Sheaf.Unused"}, "batch2"), set())

    def test_timestamp_fallback_uses_retained_batch_time(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            f = root / "lean/Sheaf/Needed.lean"
            f.parent.mkdir(parents=True)
            f.write_text("-- needed\n")
            d = snapshot(None, f.stat().st_mtime + 10, {"batch2": {}},
                         batch_times={"batch2": f.stat().st_mtime - 10})
            with patch.object(sr, "R", root), patch.object(sr, "_SNAPSHOTS", {d["t"]: d}):
                self.assertEqual(sr.changed_since(d["t"], {"Sheaf.Needed"}, "batch2"), {"Sheaf.Needed"})
                self.assertEqual(sr.changed_since(d["t"], {"Sheaf.Needed"}), set())


if __name__ == "__main__":
    unittest.main()
