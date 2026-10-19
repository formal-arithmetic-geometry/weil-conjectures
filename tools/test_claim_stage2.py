"""Claims must recheck completed stage-2 nodes when queue.tsv is stale."""
import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

import claim
import dag_queue


class Stage2ClaimTest(unittest.TestCase):
    item = "lem-stage2-claim-test"

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = pathlib.Path(temp.name)
        self.work = self.root / "coord"
        self.nodes = self.root / "dag" / "nodes"
        (self.work / "claims").mkdir(parents=True)
        (self.nodes / "test").mkdir(parents=True)
        for patcher in (
            patch.object(claim, "WORK", self.work),
            patch.object(claim, "C", self.work / "claims"),
            patch.object(claim, "RETURNS", self.work / "returns"),
            patch.object(claim, "PARKED", self.work / "stage2-parked.md"),
            patch.object(claim.li, "ROOT", self.root),
            patch.object(claim.li, "LEAN", self.root / "lean"),
            patch.object(dag_queue, "nodes_dir", return_value=self.nodes),
            patch.object(dag_queue, "finished", return_value=False),
            patch.object(claim, "_delivered", return_value=False),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)
        self.output = io.StringIO()
        redirect = contextlib.redirect_stdout(self.output)
        redirect.__enter__()
        self.addCleanup(redirect.__exit__, None, None, None)
        self.write_node(self.item, lean={"module": "Sheaf.Test", "declaration": "test"})
        self.write_queue((self.item, "2"))

    def write_node(self, item, **fields):
        node = {"id": item, "status": "split", "reviewed": {"result": "pass"}}
        node.update(fields)
        (self.nodes / "test" / (item + ".json")).write_text(json.dumps(node))

    def write_queue(self, *rows):
        (self.work / "queue.tsv").write_text("".join(f"{m}\t{s}\n" for m, s in rows))

    def test_take_refuses_landed_stage2_node_in_stale_queue(self):
        self.assertFalse(claim.take("NK", self.item))
        self.assertFalse(claim.lock(self.item).exists())

    def test_take_many_refuses_landed_and_claims_unstated_node(self):
        fresh = "lem-stage2-fresh"
        self.write_node(fresh)
        self.write_queue((self.item, "2"), (fresh, "2"))
        self.assertEqual(claim.take_many([("NK", self.item), ("NK", fresh)]), 0)
        self.assertIn(f"NO\tNK\t{self.item}\t", self.output.getvalue())
        self.assertIn(f"OK\tNK\t{fresh}\n", self.output.getvalue())
        self.assertIsNone(claim.read(self.item))
        self.assertEqual(claim.read(fresh)["who"], "NK")

    def test_next_moves_past_landed_node_to_unstated_stage2_node(self):
        fresh = "lem-stage2-fresh"
        self.write_node(fresh)
        self.write_queue((self.item, "2"), (fresh, "2"))
        with patch.object(sys, "argv", ["claim.py", "next", "NK", "--stage", "2"]):
            self.assertEqual(claim.main(), 0)
        self.assertEqual(claim.held_by("NK"), [fresh])

    def test_take_accepts_split_node_without_lean(self):
        self.write_node(self.item)
        self.assertTrue(claim.take("NK", self.item))
        self.assertEqual(claim.read(self.item)["who"], "NK")

    def test_stage2_mathlib_and_convention_nodes_are_finished(self):
        for fields in ({"status": "mathlib"}, {"lean": {"convention": "notation only"}}):
            with self.subTest(fields=fields):
                claim.lock(self.item).unlink(missing_ok=True)
                self.write_node(self.item, **fields)
                self.assertFalse(claim.take("NK", self.item))
                self.assertFalse(claim.lock(self.item).exists())

    def test_released_repair_remains_claimable(self):
        notes = self.work / "repair-notes"
        notes.mkdir()
        (notes / (self.item + ".json")).write_text(json.dumps({"state": "released"}))
        with patch.object(claim, "handoff_return") as handoff:
            self.assertTrue(claim.take("NK", self.item))
        handoff.assert_called_once_with("NK", self.item)

    def test_stage1_completed_split_is_refused(self):
        self.write_node(self.item)
        self.write_queue((self.item, "1"))
        self.assertFalse(claim.take("NK", self.item))

    def test_stage1_split_with_withdrawn_review_is_claimable(self):
        self.write_node(self.item, reviewed=None)
        self.write_queue((self.item, "1"))
        self.assertTrue(claim.take("NK", self.item))


if __name__ == "__main__":
    unittest.main()
