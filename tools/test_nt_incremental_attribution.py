"""Stage-2 batch validation blames only findings a delivery introduces (2026-10-18 land2fix)."""
import pathlib, sys, unittest
from unittest.mock import patch
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import nt_incremental2 as inc
import nt_parallel2 as par


def node(nid, stmt=(), **kw):
    return dict({"id": nid, "stmt_deps": list(stmt), "proof_deps": []}, **kw)


class Attribution(unittest.TestCase):
    def setUp(self):
        # targets come from the `target` field, not the project's target list
        c = patch.object(inc.dq.li, "config", return_value={}); c.start(); self.addCleanup(c.stop)

    def test_edge_into_flagged_node_is_not_blocking(self):
        before = {"t": node("t", ["a"], target=True), "a": node("a"),
                  "x": node("x", import_flags=["unreachable"])}
        after = dict(before, a=node("a", ["x"]))
        new = inc.global_findings(after) - inc.global_findings(before)
        self.assertIn("reach: x is flagged unreachable but a target reaches it", new)
        self.assertFalse([f for f in inc.check(before, after, {"a"}) if f.startswith("reach:")])

    def test_unreached_unflagged_node_still_blocks(self):
        before = {"t": node("t", ["a"], target=True), "a": node("a", ["x"]), "x": node("x")}
        after = dict(before, a=node("a"))
        self.assertIn("reach: x is not reached from a target and is not flagged unreachable",
                      inc.check(before, after, {"a"}))

    def test_unattributed_finding_is_blamed_on_the_delivery_producing_it_alone(self):
        f = "units: u cites v, which its nodes do not reach"
        plans = [{"id": "p1", "nodes": {"a": "x"}, "row": {"item": "a"}},
                 {"id": "p2", "nodes": {"b": "y"}, "row": {"item": "b"}}]
        check = lambda ps: [f] if any(p["id"] == "p2" for p in ps) else []
        returns = []
        survivors = par.validated_survivors(plans, returns, check=check)
        self.assertEqual([p["id"] for p in survivors], ["p1"])
        self.assertEqual([r[0]["item"] for r in returns], ["b"])

    def test_interaction_only_finding_still_refuses_the_batch(self):
        plans = [{"id": "p1", "nodes": {"a": "x"}, "row": {"item": "a"}},
                 {"id": "p2", "nodes": {"b": "y"}, "row": {"item": "b"}}]
        check = lambda ps: ["units: u cites v, which its nodes do not reach"] if len(ps) == 2 else []
        with self.assertRaises(par.md.Fail):
            par.validated_survivors(plans, [], check=check)


if __name__ == "__main__":
    unittest.main()
