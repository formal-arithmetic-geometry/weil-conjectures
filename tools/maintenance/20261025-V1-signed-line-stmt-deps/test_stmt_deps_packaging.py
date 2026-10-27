"""Exercise the real stage-3 packager in disposable repositories, without Lean or SSH.

WEIL_DELIVER3_SOURCE selects the installed script or the archived pre-fix backup.
SHEAF_TOOLS selects the project's tools directory.
"""
import contextlib
from importlib.machinery import SourceFileLoader
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
TOOLS = Path(os.environ.get("SHEAF_TOOLS", "/home/ubuntu/weil-conjectures-sheaf-shared/tools"))
SOURCE = Path(os.environ.get("WEIL_DELIVER3_SOURCE", HERE / "deliver3.py"))
sys.path.insert(0, str(TOOLS))
import stage3_delivery as s3


class Packager(unittest.TestCase):
    def package(self, before, after, expect_statement_guard=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = root / "repo"
            sb = root / "weil-sandbox/V1/Sheaf.Test"
            repo.mkdir()
            (root / "worktrees/locks").mkdir(parents=True)

            def put(base, rel, content):
                p = base / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(content)

            def git(*args):
                return subprocess.run(["git", *args], cwd=repo, check=True,
                                      text=True, capture_output=True).stdout

            git("init", "-q")
            git("config", "user.name", "Test")
            git("config", "user.email", "test@example.invalid")
            module = "lean/Sheaf/Test.lean"
            node = "dag/nodes/x/test.json"
            old = "module\n\n@[expose] public section\n\ntheorem tested : True := by sorry\n"
            put(repo, module, old)
            put(repo, node, json.dumps(before))
            put(repo, "tools/stage3_delivery.py", 'PROBE = """\n-- test probe\n"""\n')
            git("add", ".")
            git("commit", "-qm", "baseline fixture")
            git("update-ref", "refs/remotes/origin/sheaf-dag", "HEAD")
            put(sb, module, old.replace("sorry", "trivial"))
            put(sb, node, json.dumps(after))
            put(sb, "report.md", "\n".join([
                "## What changed", "## Proved and sorry left", "## No longer needed",
                "## Where the brief, the DAG or earlier work was wrong"]))
            observed = []

            def preflight(*args, **kwargs):
                # Read the actual generated commit, before the packager cleans up.
                observed.append(json.loads(git("show", "HEAD:" + node)))
                return subprocess.CompletedProcess([], 0, "review class FULL\n", "")

            modules = {
                "lcompile": types.SimpleNamespace(run=lambda *a, **k: (0, "SHEAF-PROBED 1"),
                                                  modname=lambda p: "Sheaf.Test"),
                "scompile": types.SimpleNamespace(),
                "sharedrepo": types.SimpleNamespace(WT=root / "worktrees", shared=lambda _: repo,
                                                    worktree=lambda _: repo, fetch=lambda _: None),
                "srvpreflight": types.SimpleNamespace(run=preflight),
                "import_cycles": types.SimpleNamespace(refuse=lambda *a: None,
                                                       closing_cycle=lambda *a: None),
                "delivery_cache": types.SimpleNamespace(cycle_graph=lambda _: {}),
                "stage3_delivery": s3,
            }
            with patch.dict(sys.modules, modules), patch.dict(os.environ, {"DELIVER3_SLOTS": "1"}):
                loader = SourceFileLoader("stmt_deps_test_delivery", str(SOURCE))
                spec = importlib.util.spec_from_loader(loader.name, loader)
                delivery = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(delivery)
                with patch.object(delivery, "H", root), \
                     patch.object(delivery, "check_import_sources"), \
                     patch.object(delivery, "forced_adaptations", return_value=""), \
                     patch.object(sys, "argv", [str(SOURCE), "V1", "Sheaf.Test", "--no-push"]), \
                     contextlib.redirect_stdout(io.StringIO()):
                    try:
                        if expect_statement_guard:
                            with self.assertRaisesRegex(SystemExit, "without a `statement_change` record"):
                                delivery.main()
                        else:
                            delivery.main()
                    finally:
                        slot = getattr(delivery, "_DELIVER_SLOT", None)
                        if slot:
                            slot.close()
            self.assertEqual(len(observed), 0 if expect_statement_guard else 1)
            return observed[0] if observed else None

    @staticmethod
    def node():
        return {"id": "test", "statement": "The same target statement.",
                "stmt_deps": ["existing-definition"], "proof": [], "proof_deps": [],
                "tool_uses": ["keep", "obsolete"], "lean_audit": {"state": "keep"}}

    def test_dependency_addition_survives_generated_commit(self):
        before = self.node()
        after = self.node()
        after["stmt_deps"].append("definition-owner-in-delivery")
        after["proof"] = [{"text": "Use the component theorem.", "uses": ["component"]}]
        after["proof_deps"] = ["component"]
        delivered = self.package(before, after)
        self.assertEqual(delivered["stmt_deps"], after["stmt_deps"])
        self.assertEqual(delivered["statement"], before["statement"])
        self.assertEqual(delivered["proof_deps"], ["component"])

    def test_dependency_replacement_survives_generated_commit(self):
        before = self.node()
        after = self.node()
        after["stmt_deps"] = ["replacement-definition"]
        self.assertEqual(self.package(before, after)["stmt_deps"], after["stmt_deps"])

    def test_unrelated_maintainer_metadata_stays_on_base(self):
        before = self.node()
        after = self.node()
        after["stmt_deps"].append("definition-owner-in-delivery")
        after["lean_audit"] = {"state": "stale-worker-copy"}
        after["tool_uses"] = ["keep"]
        delivered = self.package(before, after)
        self.assertEqual(delivered["lean_audit"], before["lean_audit"])
        self.assertEqual(delivered["tool_uses"], ["keep"])
        self.assertEqual(delivered["stmt_deps"], after["stmt_deps"])

    def test_statement_guard_still_requires_record(self):
        before = self.node()
        after = self.node()
        after["statement"] = "A changed target statement."
        self.package(before, after, expect_statement_guard=True)


class DagValidation(unittest.TestCase):
    def findings(self, dependency, extra=None):
        before = {"id": "test", "stmt_deps": ["existing"], "proof_deps": []}
        after = dict(before, stmt_deps=["existing", dependency])
        base = {"test": before, "existing": {"id": "existing"}}
        if extra:
            base.update(extra)
        data = {"nodes": {"test": {"role": "changed", "path": "test.json",
                                   "base_node": before, "node": after}}}
        return s3.edge_fails(data, base)

    def test_known_acyclic_dependency_is_valid(self):
        self.assertEqual(self.findings("owner", {"owner": {"id": "owner"}}), [])

    def test_unknown_dependency_is_enforced(self):
        findings = self.findings("missing")
        self.assertTrue(findings)
        self.assertTrue(all(s3.enforced(f) for f in findings))

    def test_new_cycle_is_enforced(self):
        findings = self.findings("parent", {"parent": {"id": "parent", "stmt_deps": ["test"]}})
        self.assertTrue(findings)
        self.assertTrue(all(s3.enforced(f) for f in findings))


if __name__ == "__main__":
    unittest.main()
