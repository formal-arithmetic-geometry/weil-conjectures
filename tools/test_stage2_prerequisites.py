"""Stage-2 prerequisite admission through the complete delivery reader; no Lean build."""
import copy
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import stage2_delivery as s2


ITEM = "prop-weil-pbc-scalar-extension"
NEEDED = "lem-weil-pbc-uniform-complete-triangulated"
RATIONAL = "def-weil-pbc-rational-category"
HELPER = "def-maint-q10-helper"
UNRELATED = "lem-maint-q10-unrelated"


class Prerequisites(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="stage2-prerequisites-")
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Bin Wu")
        self.git("config", "user.email", "844524296@qq.com")
        # Q10's rational-category statement dependency has no edge to NEEDED.
        self.nodes = {
            ITEM: self.node(ITEM, [RATIONAL], [NEEDED]),
            RATIONAL: self.node(RATIONAL),
            NEEDED: self.node(NEEDED, [HELPER]),
            HELPER: self.node(HELPER),
            UNRELATED: self.node(UNRELATED),
        }

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.root, capture_output=True, text=True,
            check=True).stdout.strip()

    def node(self, nid, stmt=(), proof=()):
        return {"id": nid, "kind": "lemma", "status": "split",
                "statement": "The fixture statement is true.",
                "stmt_deps": list(stmt), "proof_deps": list(proof)}

    def path(self, nid):
        return f"dag/nodes/sec-proper-base-change/{nid}.json"

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def write_node(self, node):
        self.write(self.path(node["id"]), json.dumps(node, indent=1) + "\n")

    def base(self):
        for node in self.nodes.values():
            self.write_node(node)
        self.git("add", ".")
        self.git("commit", "-qm", "prerequisite fixture base")
        self.git("branch", "sheaf-dag")

    def module(self, nid, name):
        node = copy.deepcopy(self.nodes[nid])
        module = "Sheaf.Stage2.MaintQ10" + name
        decl = "maintQ10" + name
        path = "lean/" + module.replace(".", "/") + ".lean"
        self.write(path, f"/-- Source: regression fixture (blueprint: {nid}).\n"
                   f"Proof: True has its canonical inhabitant. -/\n"
                   f"theorem {decl} : True := by sorry\n")
        node["lean"] = {
            "module": module, "file": path, "declaration": decl,
            "statement": f"theorem {decl} : True", "existing": False,
            "branch": "sheaf-dag", "by": "Q10", "date": "2026-10-16",
            "note": "The existing prerequisite has no recorded Lean declaration.",
        }
        self.write_node(node)
        return node

    def delivery(self, cite=False, deps=(NEEDED,), mutate=False):
        item = self.module(ITEM, "Item")
        if cite:
            item["stmt_deps"] += list(deps)
            self.write_node(item)
        for index, nid in enumerate(deps):
            node = self.module(nid, "Dependency" + str(index))
            if mutate:
                node["statement"] = "An unauthorized change to a dependency."
                self.write_node(node)
        self.write(f"coord/reports/Q10/{ITEM}.md",
                   "## Worker report\nFixture for prerequisite classification.\n\n"
                   "## Second reading by Q10\nFixture report for reader checks.\n\n"
                   "## Dependency modules\n" + "\n".join(deps) + "\n")
        self.git("add", ".")
        self.git("commit", "-qm", "prerequisite fixture delivery")
        return s2.read_delivery(s2.Git(self.root), "HEAD", "sheaf-dag", "Q10", ITEM)

    def test_item_proof_prerequisite_with_lean_only_repair(self):
        self.base()
        result = self.delivery()
        self.assertEqual(result["fails"], [])
        self.assertIn(NEEDED, result["deps"])
        self.assertFalse(result["corrected"])

    def test_item_proof_prerequisite_also_added_to_stmt_deps(self):
        self.base()
        result = self.delivery(cite=True)
        self.assertEqual(result["fails"], [])
        self.assertIn(NEEDED, result["deps"])
        self.assertIn(NEEDED, result["added_deps"])
        self.assertFalse(result["corrected"])

    def test_transitive_prerequisite_of_item_proof_dependency(self):
        self.base()
        result = self.delivery(deps=(HELPER,))
        self.assertEqual(result["fails"], [])
        self.assertIn(HELPER, result["deps"])

    def test_transitive_proof_edge_in_delivered_prerequisite(self):
        self.nodes[NEEDED]["stmt_deps"] = []
        self.nodes[NEEDED]["proof_deps"] = [HELPER]
        self.base()
        result = self.delivery(deps=(NEEDED, HELPER))
        self.assertEqual(result["fails"], [])

    def test_original_statement_prerequisite_still_allowed(self):
        self.base()
        result = self.delivery(deps=(RATIONAL,))
        self.assertEqual(result["fails"], [])

    def test_newly_cited_existing_prerequisite_supplied_in_delivery(self):
        self.base()
        result = self.delivery(cite=True, deps=(UNRELATED,))
        self.assertEqual(result["fails"], [])
        self.assertIn(UNRELATED, result["deps"])

    def test_unstated_citation_without_supplied_module_still_rejected(self):
        self.base()
        item = self.nodes[ITEM]
        item["stmt_deps"].append(UNRELATED)
        result = self.delivery()
        self.assertTrue(any(letter == "b" and "stmt_deps gained" in message
                            for letter, message in result["fails"]), result["fails"])

    def test_unrelated_uncited_node_still_rejected(self):
        self.base()
        result = self.delivery(deps=(UNRELATED,))
        self.assertNotIn(UNRELATED, result["deps"])
        self.assertTrue(any(letter == "b" and UNRELATED in message
                            for letter, message in result["fails"]), result["fails"])

    def test_dependency_statement_change_still_rejected(self):
        self.base()
        result = self.delivery(mutate=True)
        self.assertTrue(any(letter == "b" and "changed in field(s) statement" in message
                            for letter, message in result["fails"]), result["fails"])

    def test_large_cyclic_prerequisite_closure_is_not_truncated(self):
        # Q13's 11,440-node closure exceeded the old 3,000-node cutoff. Go past
        # its temporary 50,000 replacement too. Keep the large read-only graph
        # in memory; the item, delivery commit and repaired node remain real Git.
        ids = [f"lem-maint-q13-chain-{i}" for i in range(50001)]
        self.nodes[ITEM]["proof_deps"] = [ids[0]]
        self.base()
        virtual = {}
        for i, nid in enumerate(ids):
            following = [ids[i + 1]] if i + 1 < len(ids) else [ids[0], NEEDED]
            field = "stmt_deps" if i % 2 == 0 else "proof_deps"
            virtual[self.path(nid)] = json.dumps({"id": nid, field: following})
        original_run, original_show = s2.Git.run, s2.Git.show

        def run(git, *args, **kwargs):
            text = original_run(git, *args, **kwargs)
            if args[:3] == ("ls-tree", "-r", "--name-only"):
                text += "\n" + "\n".join(virtual)
            return text

        def show(git, revision, path):
            if path in virtual:
                return virtual[path]
            return original_show(git, revision, path)

        with patch.object(s2.Git, "run", run), patch.object(s2.Git, "show", show):
            result = self.delivery(deps=(NEEDED, HELPER))
        self.assertEqual(result["fails"], [])
        self.assertIn(NEEDED, result["deps"])
        self.assertIn(HELPER, result["deps"])


if __name__ == "__main__":
    unittest.main()
