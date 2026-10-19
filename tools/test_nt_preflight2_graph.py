"""Dry runs must reject the dependency cycles that landing would reject."""
import copy
import pathlib
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import nt_preflight2 as preflight


ITEM = "lem-coef-infinity-pointwise-yoneda-evaluation"
COMPARISON = "lem-coef-coherent-nerve-comparison"
MODEL = "lem-coef-model-colimit-localization-comparison"
RECTIFICATION = "lem-coef-small-diagram-model-rectification"
ADJOINT = "lem-coef-infinity-pointwise-adjoint-criterion"
FOUNDATION = "def-cbc-enhanced-diagrams-cones"


def node(nid, stmt=(), proof=()):
    return {"id": nid, "stmt_deps": list(stmt), "proof_deps": list(proof)}


class PreflightGraph(unittest.TestCase):
    def setUp(self):
        # The actual return path: adding ITEM -> COMPARISON closes this cycle.
        self.before = {
            ITEM: node(ITEM, [FOUNDATION]),
            FOUNDATION: node(FOUNDATION),
            COMPARISON: node(COMPARISON, proof=[MODEL]),
            MODEL: node(MODEL, proof=[RECTIFICATION]),
            RECTIFICATION: node(RECTIFICATION, proof=[ADJOINT]),
            ADJOINT: node(ADJOINT, [ITEM]),
        }
        self.delivery = {"node": copy.deepcopy(self.before[ITEM]), "rec": {},
                         "corrected": False, "added_deps": [], "new": {}, "deps": {}}

    def findings(self):
        return preflight.graph_findings(self.delivery, self.before)

    def test_default_baseline_uses_published_side_dag_not_live_overlay(self):
        dependency = "lem-coef-enriched-diagram-size-generation"
        self.before[ITEM]["proof_deps"] = [dependency]
        self.before[dependency] = node(dependency)
        live = {ITEM: copy.deepcopy(self.before[ITEM])}
        # coord/sheaf.env selects this live graph; it has no side-only dependency.
        with patch.object(preflight.nt_incremental2.dq, "load", return_value=live) as live_load, \
                patch.object(preflight.s2, "nodes_at", return_value=self.before) as published:
            self.assertEqual(preflight.graph_findings(self.delivery), [])
        live_load.assert_not_called()
        self.assertEqual(published.call_count, 1)
        git, ref = published.call_args.args
        self.assertEqual(git.root, preflight.s2.ROOT)
        self.assertEqual(ref, "sheaf-dag")

    def test_default_baseline_still_rejects_node_missing_on_side_branch(self):
        dependency = "def-maint-live-only"
        self.before[ITEM]["proof_deps"] = [dependency]
        live = dict(self.before, **{dependency: node(dependency)})
        with patch.object(preflight.nt_incremental2.dq, "load", return_value=live), \
                patch.object(preflight.s2, "nodes_at", return_value=self.before):
            self.assertEqual(preflight.graph_findings(self.delivery),
                             [f"deps: {ITEM} (proof) -> {dependency}: no such node"])

    def test_returned_yoneda_edge_is_rejected(self):
        self.delivery["added_deps"] = [COMPARISON]
        self.assertEqual(self.findings(), [f"cycles: {ITEM} -> {COMPARISON} reaches {ITEM}"])

    def test_infrastructure_dependency_is_acyclic(self):
        infrastructure = "def-coef-coherent-nerve-infrastructure"
        self.before[infrastructure] = node(infrastructure, [FOUNDATION])
        self.delivery["added_deps"] = [infrastructure]
        self.assertEqual(self.findings(), [])

    def test_current_server_edges_are_checked_after_merge_base(self):
        self.delivery["added_deps"] = [COMPARISON]
        # An earlier snapshot did not yet have this route back to the item.
        self.before[ADJOINT]["stmt_deps"] = []
        self.assertEqual(self.findings(), [])
        self.before[ADJOINT]["stmt_deps"] = [ITEM]
        self.assertTrue(self.findings())

    def test_lean_only_dependency_repair_preserves_current_edges(self):
        self.delivery["added_deps"] = [COMPARISON]
        self.delivery["deps"] = {COMPARISON: {
            "node": dict(node(COMPARISON), lean={"declaration": "Fixture.comparison"})}}
        self.assertTrue(self.findings())

    def test_stale_item_copy_does_not_restore_removed_edges(self):
        self.delivery["node"]["stmt_deps"].append(COMPARISON)
        self.assertEqual(self.findings(), [])

    def test_source_based_statement_correction_can_remove_cycle(self):
        self.before[ITEM]["stmt_deps"].append(COMPARISON)
        self.delivery["corrected"] = True
        self.assertEqual(self.findings(), [])

    def test_inherited_cycle_through_touched_node_still_blocks(self):
        self.before[ITEM]["stmt_deps"].append(COMPARISON)
        self.assertTrue(self.findings())

    def test_new_helper_that_closes_cycle_is_rejected(self):
        helper = "def-maint-yoneda-helper"
        self.delivery["added_deps"] = [helper]
        self.delivery["new"] = {helper: {"node": node(helper, [ITEM])}}
        self.assertEqual(len(self.findings()), 2)
        self.assertTrue(all(f.startswith("cycles:") for f in self.findings()))

    def test_missing_node_is_reported(self):
        self.delivery["added_deps"] = ["def-maint-missing"]
        self.assertEqual(self.findings(), [f"deps: {ITEM} (stmt) -> def-maint-missing: no such node"])

    def test_read_only_check_leaves_input_records_unchanged(self):
        self.delivery["added_deps"] = [COMPARISON]
        original = copy.deepcopy((self.before, self.delivery))
        self.findings()
        self.assertEqual((self.before, self.delivery), original)

    def test_bad_item_is_already_reported_by_delivery_reader(self):
        self.delivery["node"] = None
        self.assertEqual(self.findings(), [])

    def test_unrelated_existing_cycle_does_not_block_item(self):
        a, b = "lem-maint-unrelated-a", "lem-maint-unrelated-b"
        self.before.update({a: node(a, [b]), b: node(b, [a])})
        self.assertEqual(self.findings(), [])


if __name__ == "__main__":
    unittest.main()
