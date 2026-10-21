"""A human's released re-split must be queued even when its Lean is closed."""
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import assumed
import dag_queue
import units


class ReleasedStage1Repair(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = pathlib.Path(temp.name)
        self.notes = self.root / "coord" / "repair-notes"
        self.notes.mkdir(parents=True)
        (self.root / "targets.txt").write_text("target\n")
        for patcher in (
            patch.object(dag_queue.li, "ROOT", self.root),
            patch.object(dag_queue.li, "config", return_value={"SHEAF_TARGET_LIST": "targets.txt"}),
            patch.object(dag_queue, "_NOTES", {}),
            patch.object(dag_queue, "_ASSUMED", {}),
            patch.object(assumed, "nodes", return_value={}),
            patch.object(units, "route", return_value=[]),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)

    def node(self, item, *, closed=False, **fields):
        result = {"id": item, "status": "split", "reviewed": {"result": "pass"}}
        if closed:
            result["lean_audit"] = {"slopmaster2": {"state": "closed"}}
        result.update(fields)
        return result

    def note(self, item, *, state="released", stage="1"):
        (self.notes / (item + ".json")).write_text(json.dumps({
            "item": item, "state": state, "stage": stage, "reason": "human re-split",
        }))

    def queued(self, nodes):
        return {item for _, item in dag_queue.Dag(nodes).stage1()}

    def test_closed_reached_node_with_released_resplit_is_queued(self):
        nodes = {
            "target": self.node("target", proof_deps=["repair"]),
            "repair": self.node("repair", closed=True),
            "unrelated": self.node("unrelated", closed=True),
        }
        self.note("repair")
        self.note("unrelated")
        self.assertEqual(self.queued(nodes), {"repair"})

    def test_closed_repair_in_statement_downstream_is_queued(self):
        # A closed target cuts dist1, but its needed statement can be reopened.
        nodes = {
            "target": self.node("target", closed=True, stmt_deps=["repair"]),
            "repair": self.node("repair", closed=True),
        }
        self.note("repair")
        self.assertEqual(self.queued(nodes), {"repair"})

    def test_resolving_note_removes_closed_node_from_queue(self):
        nodes = {"target": self.node("target", closed=True)}
        self.note("target")
        self.assertEqual(self.queued(nodes), {"target"})
        self.note("target", state="resolved")
        self.assertEqual(self.queued(nodes), set())

    def test_completed_node_without_repair_stays_closed(self):
        self.assertEqual(self.queued({"target": self.node("target", closed=True)}), set())

    def test_stage3_note_does_not_reopen_stage1(self):
        self.note("target", stage="3")
        self.assertEqual(self.queued({"target": self.node("target", closed=True)}), set())

    def test_ordinary_unsplit_and_reviewed_nodes_keep_their_roles(self):
        nodes = {
            "target": self.node("target", proof_deps=["todo", "reviewed"]),
            "todo": self.node("todo", status="unsplit", reviewed=None),
            "reviewed": self.node("reviewed"),
        }
        self.assertEqual(self.queued(nodes), {"todo"})


if __name__ == "__main__":
    unittest.main()
