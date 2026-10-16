"""Regression for reviewer-required tool_uses pruning through stage-3 delivery.

Uses temporary repositories and fake compiler/landing processes; never runs Lean.
"""
import copy
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import stage3_delivery as s3


def node(tools):
    return {"id": "a", "tool_uses": tools, "lean_audit": {"state": "keep"}}


def node_findings(before, after):
    findings = []
    data = {"modules": [], "nodes": {"a": {
        "role": "changed", "path": "dag/nodes/x/a.json", "base_node": before, "node": after}}}
    s3.check_nodes(data, lambda *x: findings.append(x), None, "base", "C3", "Sheaf.A", {})
    return findings


class Pruning(unittest.TestCase):
    def test_preflight_accepts_only_deletions(self):
        before = node(["keep", "obsolete", "last"])
        for after in (node(["keep", "last"]), node([]), node(None), {"id": "a", "lean_audit": {"state": "keep"}}):
            with self.subTest(after=after):
                self.assertEqual(node_findings(before, after), [])
        for tools in (["keep", "new"], ["last", "keep"], ["keep", "keep"], "keep", {"keep": True}):
            with self.subTest(tools=tools):
                self.assertTrue(node_findings(before, node(tools)))
        self.assertTrue(node_findings(node([]), node(["new"])))
        after = node(["keep", "last"])
        after["lean_audit"] = {"state": "forbidden"}
        self.assertTrue(node_findings(before, after))

    def test_three_way_landing_keeps_new_approvals_and_audit(self):
        before = node(["keep", "obsolete", "last"])
        current = node(["keep", "obsolete", "last", "new-on-tip"])
        original = copy.deepcopy(before)
        s3.apply_tool_uses_pruning(current, before, node(["keep", "last"]))
        self.assertEqual(current, node(["keep", "last", "new-on-tip"]))
        self.assertEqual(before, original)
        s3.apply_tool_uses_pruning(current, before, {"id": "a"})
        self.assertEqual(current, node(["new-on-tip"]))

    def test_empty_null_and_absent_field(self):
        for after in ({"tool_uses": []}, {"tool_uses": None}, {}):
            current = node(["obsolete"])
            s3.apply_tool_uses_pruning(current, node(["obsolete"]), after)
            self.assertEqual(current.get("tool_uses"), [] if after.get("tool_uses") == [] else None)
        current = node(["same", "same"])
        s3.apply_tool_uses_pruning(current, copy.deepcopy(current), node(["same"]))
        self.assertEqual(current["tool_uses"], ["same"])


class Pipeline(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)

    def put(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        return p

    def test_real_packager_keeps_pruning_in_its_commit(self):
        snapshot = pathlib.Path(os.environ.get("WEIL_DELIVER3_SOURCE", pathlib.Path(__file__).parent /
            "maintenance/20261016-stage3-tool-pruning/deliver3.py"))
        fake_compile = types.SimpleNamespace(run=lambda *a, **k: (0, "SHEAF-PROBED 1"),
            modname=lambda p: "Sheaf.A")
        fake_shared = types.SimpleNamespace(WT=self.root / "worktrees",
            worktree=lambda _: self.root / "repo", fetch=lambda _: None)
        (fake_shared.WT / "locks").mkdir(parents=True)
        imports = types.SimpleNamespace(refuse=lambda *a: None, closing_cycle=lambda *a: None)
        modules = {"lcompile": fake_compile, "scompile": types.SimpleNamespace(),
            "sharedrepo": fake_shared, "import_cycles": imports,
            "delivery_cache": types.SimpleNamespace(cycle_graph=lambda _: {})}
        with patch.dict(sys.modules, modules):
            spec = importlib.util.spec_from_file_location("delivery_pruning_test", snapshot)
            delivery = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(delivery)
            repo = self.root / "repo"
            repo.mkdir()
            real_run = subprocess.run

            def git(*args):
                return real_run(["git", *args], cwd=repo, check=True, capture_output=True, text=True)

            git("init", "-q")
            git("config", "user.name", "Test")
            git("config", "user.email", "test@example.invalid")
            rel = "lean/Sheaf/A.lean"
            old = "module\n\n@[expose] public section\n\ntheorem tested : True := by sorry\n"
            self.put("repo/" + rel, old)
            self.put("repo/dag/nodes/x/a.json", json.dumps(node(["keep", "obsolete"])))
            self.put("repo/tools/stage3_delivery.py", pathlib.Path(s3.__file__).read_text())
            git("add", ".")
            git("commit", "-qm", "base")
            git("update-ref", "refs/remotes/origin/sheaf-dag", "HEAD")
            sb = "weil-sandbox/C3/Sheaf.A/"
            self.put(sb + rel, old.replace("sorry", "trivial"))
            self.put(sb + "dag/nodes/x/a.json", json.dumps(node(["keep"])))
            self.put(sb + "report.md", "\n".join(delivery.SECTIONS))
            observed = []

            def run(args, **kwargs):
                if len(args) > 1 and args[1] == "tools/preflight_delivery.py":
                    packaged = json.loads(git("show", "HEAD:dag/nodes/x/a.json").stdout)
                    self.assertEqual(packaged, node(["keep"]))
                    self.assertEqual(node_findings(node(["keep", "obsolete"]), packaged), [])
                    observed.append(packaged)
                    return subprocess.CompletedProcess(args, 0, "review class: CODEX: changes a node file\n", "")
                return real_run(args, **kwargs)

            with patch.object(delivery, "H", self.root), patch.object(delivery, "check_import_sources"), \
                 patch.object(delivery, "forced_adaptations", return_value=""), \
                 patch.object(subprocess, "run", side_effect=run), \
                 patch.object(sys, "argv", ["deliver3.py", "C3", "Sheaf.A", "--no-push"]):
                delivery.main()
            self.assertEqual(len(observed), 1)

    def test_real_lander_applies_pruning_to_current_node(self):
        with patch.dict(os.environ, {"SHEAF_LEAD": "L-only"}):
            import batch_land as bl
        (self.root / "local/requests").mkdir(parents=True)
        np = "dag/nodes/x/a.json"
        self.put(np, json.dumps(node(["keep", "obsolete", "new-on-tip"])))
        before, after = node(["keep", "obsolete"]), node(["keep"])
        data = {"modules": [], "nodes": {"a": {"role": "changed", "path": np,
            "base_node": before, "node": after}}, "changes": {}, "commits": [],
            "report_path": "coord/reports/C3/Sheaf.A.md", "report": "reviewed"}
        plan = {"group": "C3", "item": "Sheaf.A", "head": "delivery-head", "D": data,
            "reviewer": "independent-reader", "verdict": "PASS", "cur": {}, "write": [], "item_nodes": []}

        def run(args, **kwargs):
            output = "landing-id\n" if "begin" in args else "proof\n"
            return subprocess.CompletedProcess(args, 0, output, "")

        with patch.object(bl, "ROOT", self.root), patch.object(bl, "BD", self.root / "local/batch"), \
             patch.object(bl.md, "ROOT", self.root), patch.object(bl.md, "has_ref", return_value=True), \
             patch.object(bl.md, "git", return_value="delivery-head"), patch.object(bl.md, "git_retry"), \
             patch.object(bl.md, "ledger_line", return_value="test"), \
             patch.object(bl.md, "return_entries", return_value=(self.root / "coord/returns/C3.md", None, [])), \
             patch.object(bl.ld, "REQUESTS", self.root / "local/requests"), \
             patch.object(bl, "marker", return_value=self.root / "passed"), \
             patch.object(subprocess, "run", side_effect=run):
            bl.land_one(plan, "test-batch")
        landed = json.loads((self.root / np).read_text())
        self.assertEqual(landed["tool_uses"], ["keep", "new-on-tip"])
        self.assertEqual(landed["lean_audit"], before["lean_audit"])
        self.assertEqual(landed["reviewed_proof"]["reviewer"], "independent-reader")


if __name__ == "__main__":
    unittest.main()
