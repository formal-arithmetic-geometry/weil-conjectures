"""Regressions for metadata on a newly imported blueprint snapshot."""
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import units


class SnapshotBuildTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.bp = self.root / "literature/blueprint/main-20261015/blueprint"
        self.sec = self.bp / "sec-new"
        self.sec.mkdir(parents=True)
        (self.sec / "_section.md").write_text('+++\ntitle = "Chapter"\nuses = ["sec-old"]\n+++\nChapter text.\n')
        self.unit = self.sec / "sk-new"
        self.unit.mkdir()
        (self.unit / "_section.md").write_text('+++\ntitle = "Unit"\nuses = ["sk-definition"]\n+++\nStatement.\n')
        (self.unit / "sk-new.proof.md").write_text('+++\nkind = "proof"\nof = "sk-new"\n+++\nFirst step.\n\nSecond step.\n')
        other = self.sec / "sk-other"
        other.mkdir()
        (other / "_section.md").write_text('+++\ntitle = "Other"\n+++\nOther statement.\n')
        self.nodes_dir = self.root / "dag/nodes"
        self.node = self.nodes_dir / "sec-new/sk-new.json"
        self.node.parent.mkdir(parents=True)
        self.node.write_text(json.dumps({"id": "sk-new", "source": {"document": str((self.unit / "_section.md").relative_to(self.root))}, "chapter": None, "unit": None}))
        self.other = self.node.with_name("sk-other.json")
        self.other.write_text(json.dumps({"id": "sk-other", "source": {"document": str((other / "_section.md").relative_to(self.root))}, "chapter": None, "unit": None}))
        self.old = self.root / "dag/units/sk-old.json"
        self.old.parent.mkdir(parents=True)
        self.old.write_text('{"id":"sk-old","realized":{"statement":["kept"],"steps":[]}}\n')
        self.patches = [patch.object(units, "ROOT", self.root),
                        patch.object(units, "UNITS", self.root / "dag/units"),
                        patch.object(units, "CHAPTERS", self.root / "dag/chapters"),
                        patch.object(units.dq, "nodes_dir", return_value=self.nodes_dir),
                        patch.object(units.dq, "load", side_effect=lambda: {p.stem: json.loads(p.read_text()) for p in self.nodes_dir.rglob("*.json")})]
        for p in self.patches:
            p.start()
            self.addCleanup(p.stop)

    def build(self):
        units.build(self.bp, {"sk-new"})

    def record(self):
        return json.loads((units.UNITS / "sk-new.json").read_text())

    def test_companion_proof_and_source_are_recorded(self):
        self.build()
        rec = self.record()
        self.assertEqual(rec["steps"], [{"text": "First step."}, {"text": "Second step."}])
        self.assertEqual(rec["realized"], {"statement": [], "steps": [[], []]})
        self.assertEqual(rec["uses"], ["sk-definition"])
        self.assertIn("main-20261015", rec["source"])
        self.assertEqual(json.loads(self.node.read_text())["unit"], "sk-new")
        chapter = json.loads((units.CHAPTERS / "sec-new.json").read_text())
        self.assertEqual(chapter["uses"], ["sec-old"])

    def test_selected_build_leaves_other_units_and_nodes_untouched(self):
        old, other = self.old.read_bytes(), self.other.read_bytes()
        self.build()
        self.assertEqual(self.old.read_bytes(), old)
        self.assertEqual(self.other.read_bytes(), other)
        self.assertFalse((units.UNITS / "sk-other.json").exists())

    def test_realization_is_preserved_and_repeat_is_noop(self):
        self.build()
        path = units.UNITS / "sk-new.json"
        rec = self.record()
        rec["realized"] = {"statement": ["carrier"], "steps": [["carrier"], ["carrier"]]}
        rec["realized_by"] = {"item": "carrier", "date": "2026-10-16"}
        path.write_text(json.dumps(rec, ensure_ascii=False, indent=1) + "\n")
        before = path.read_bytes()
        backups = sorted(str(p) for p in self.root.rglob("*.bak"))
        self.build()
        self.assertEqual(path.read_bytes(), before)
        self.assertEqual(sorted(str(p) for p in self.root.rglob("*.bak")), backups)

    def test_inline_proof_takes_precedence(self):
        with (self.unit / "_section.md").open("a") as f:
            f.write("\n## Proof\nInline proof.\n")
        self.build()
        self.assertEqual(self.record()["steps"], [{"text": "Inline proof."}])

    def test_missing_selection_fails_without_writes(self):
        before = {str(p): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        with self.assertRaisesRegex(ValueError, "absent"):
            units.build(self.bp, {"sk-missing"})
        self.assertEqual(before, {str(p): p.read_bytes() for p in self.root.rglob("*") if p.is_file()})

    def test_backup_contains_original_node(self):
        original = self.node.read_bytes()
        self.build()
        self.assertEqual(self.node.with_name(self.node.name + units.BACKUP_SUFFIX).read_bytes(), original)

    def test_created_node_inherits_selected_item(self):
        child = self.node.with_name("child.json")
        child.write_text(json.dumps({"id": "child", "created": {"item": "sk-new"}}))
        self.build()
        self.assertEqual(json.loads(child.read_text())["unit"], "sk-new")

    def test_master_and_current_sources_are_both_understood(self):
        chapters = {"sec-new", "sec-old"}
        files = {"current": self.node, "old": self.old, "child": self.other}
        nodes = {"current": {"source": {"document": "literature/blueprint/main-20261015/blueprint/sec-new/sk-new/_section.md"}},
                 "old": {"source": {"document": "literature/blueprint/master/blueprint/sec-old/sk-old/_section.md"}},
                 "child": {"created": {"item": "current"}}}
        records = {"sk-new", "sk-old"}
        self.assertEqual(units.node_place("current", nodes, files, records, chapters), ("sec-new", "sk-new"))
        self.assertEqual(units.node_place("old", nodes, files, records, chapters), ("sec-old", "sk-old"))
        self.assertEqual(units.node_place("child", nodes, files, records, chapters), ("sec-new", "sk-new"))

    def test_live_sync_restores_missing_metadata_but_keeps_explicit_bindings(self):
        node = json.loads(self.node.read_text())
        units.stamp_missing(node, {"sk-new"}, {"sec-new"})
        self.assertEqual((node["chapter"], node["unit"]), ("sec-new", "sk-new"))
        node.update(chapter="live-chapter", unit="live-unit")
        units.stamp_missing(node, {"sk-new"}, {"sec-new"})
        self.assertEqual((node["chapter"], node["unit"]), ("live-chapter", "live-unit"))

    def test_live_sync_does_not_name_missing_records(self):
        node = json.loads(self.node.read_text())
        units.stamp_missing(node, set(), set())
        self.assertIsNone(node["chapter"])
        self.assertIsNone(node["unit"])

    def test_build_never_writes_the_read_overlay(self):
        external = self.root / "external-live"
        external.mkdir()
        live = external / "sk-new.json"
        live.write_bytes(self.node.read_bytes())
        before = live.read_bytes()
        with patch.object(units.dq, "nodes_dir", return_value=external), \
                patch.object(units.dq, "load", return_value={"sk-new": json.loads(before)}):
            self.build()
        self.assertEqual(live.read_bytes(), before)
        self.assertEqual(json.loads(self.node.read_text())["unit"], "sk-new")


if __name__ == "__main__":
    unittest.main()
