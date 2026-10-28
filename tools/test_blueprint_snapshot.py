"""Regressions of the blueprint refresh (~/cc1/blueprint-refresh.sh, tools/blueprint_snapshot.py).

2026-10-28: the import of main-20261028 died in units.node_place on a node whose `source` is a plain path
(AttributeError: 'str' object has no attribute 'get'), after units.build had overwritten chapter records and left .bak
files; the refresh now follows the blueprint pointer of weil-conjectures slopmaster2.
"""
import io
import json
import os
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import blueprint_snapshot as bs
import units


class SourceDocumentTests(unittest.TestCase):
    def test_dict_str_and_missing_sources(self):
        doc = "literature/blueprint/x/blueprint/sec-a/sk-a/_section.md"
        self.assertEqual(units.source_document({"source": {"document": doc}}), doc)
        self.assertEqual(units.source_document({"source": doc}), doc)
        self.assertEqual(units.source_document({"source": None}), "")
        self.assertEqual(units.source_document({}), "")
        self.assertEqual(units.source_document({"source": ["odd"]}), "")

    def test_node_place_with_plain_path_source(self):
        nodes = {"n": {"id": "n", "source": "literature/stacks-project/sites-cohomology.tex"}}
        files = {"n": pathlib.Path("dag/nodes/sec-a/n.json")}
        self.assertEqual(units.node_place("n", nodes, files, {"sk-a"}, {"sec-a"}), ("sec-a", None))
        d = {"source": "literature/blueprint/s/blueprint/sec-a/sk-a/lem.md"}
        self.assertEqual(units.stamp_missing(d, {"sk-a"}, {"sec-a"}), dict(d, chapter="sec-a", unit="sk-a"))


class BuildWithPlainSourceNodeTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.bp = self.root / "literature/blueprint/slopmaster2-20261028/blueprint"
        unit = self.bp / "sec-a/sk-new"
        unit.mkdir(parents=True)
        (self.bp / "sec-a/_section.md").write_text('+++\ntitle = "A"\n+++\nNew chapter text.\n')
        (unit / "_section.md").write_text('+++\ntitle = "New"\n+++\nStatement.\n')
        nodes = self.root / "dag/nodes/sec-a"
        nodes.mkdir(parents=True)
        (nodes / "plain.json").write_text(json.dumps({"id": "plain", "source": "literature/stacks-project/x.tex"}))
        (nodes / "sk-new.json").write_text(json.dumps(
            {"id": "sk-new", "source": {"document": str((unit / "_section.md").relative_to(self.root))}}))
        self.chapter = self.root / "dag/chapters/sec-a.json"
        self.chapter.parent.mkdir(parents=True)
        self.chapter.write_text('{"id": "sec-a", "text": "old chapter text"}\n')
        (self.root / "dag/units").mkdir(parents=True)
        for p in (patch.object(units, "ROOT", self.root), patch.object(units, "UNITS", self.root / "dag/units"),
                  patch.object(units, "CHAPTERS", self.root / "dag/chapters"), patch.object(bs, "ROOT", self.root),
                  patch.object(bs, "NODES", self.root / "dag/nodes")):
            p.start()
            self.addCleanup(p.stop)

    def test_build_does_not_fail_on_plain_path_source(self):
        with patch("sys.stdout", io.StringIO()):
            units.build(self.bp, {"sk-new"})
        self.assertEqual(json.loads((self.root / "dag/nodes/sec-a/sk-new.json").read_text())["unit"], "sk-new")

    def test_write_units_keeps_chapters_and_leaves_no_bak(self):
        before = self.chapter.read_bytes()
        with patch("sys.stdout", io.StringIO()):
            written, want = bs.write_units(self.bp.parent, ["sk-new"])
        self.assertEqual(want, ["sk-new"])
        self.assertEqual(self.chapter.read_bytes(), before)
        self.assertEqual(list(self.root.rglob("*.bak")), [])

    def test_write_units_restores_chapters_when_build_fails(self):
        before = self.chapter.read_bytes()

        def broken(bp, selected):
            self.chapter.write_text("overwritten")
            self.chapter.with_name("sec-a.json.units-1.bak").write_bytes(before)
            raise AttributeError("'str' object has no attribute 'get'")
        with patch.object(units, "build", broken), self.assertRaises(AttributeError):
            bs.write_units(self.bp.parent, ["sk-new"])
        self.assertEqual(self.chapter.read_bytes(), before)
        self.assertEqual(list(self.root.rglob("*.bak")), [])


class SnapshotRecordTests(unittest.TestCase):
    def test_recorded_reads_main_and_slopmaster2_snapshots(self):
        with tempfile.TemporaryDirectory() as t:
            c = pathlib.Path(t) / "COMMITS.txt"
            c.write_text("master 967 slopmaster2 1ad\nmain-20261026 a88 (x)\nslopmaster2-20261028 4b8 (y)\n")
            with patch.object(bs, "COMMITS", c):
                self.assertEqual(bs.recorded(), [("main-20261026", "a88"), ("slopmaster2-20261028", "4b8")])

    def test_current_snapshot_follows_latest(self):
        with tempfile.TemporaryDirectory() as t:
            lit = pathlib.Path(t)
            (lit / "slopmaster2-20261028").mkdir()
            os.symlink("slopmaster2-20261028", lit / "latest")
            with patch.object(units, "LIT", lit):
                self.assertEqual(units.current_snapshot(), lit / "slopmaster2-20261028")
                self.assertEqual(units.current_snapshot("main-20261026"), lit / "main-20261026")


class PointerTests(unittest.TestCase):
    def fetch(self, payload):
        class R(io.BytesIO):
            def __enter__(self):
                return self

            def __exit__(self, *a):
                return False
        seen = []

        def f(req, timeout=None):
            seen.append(req)
            return R(json.dumps(payload).encode())
        return f, seen

    def test_pointer_reads_the_submodule_of_slopmaster2(self):
        sha = "4b8d51db17ebc92358cdf5f2e7722bd6008bf131"
        f, seen = self.fetch({"type": "submodule", "sha": sha})
        self.assertEqual(bs.pointer(f), sha)
        self.assertIn("weil-conjectures/contents/blueprint?ref=slopmaster2", seen[0].full_url)

    def test_pointer_refuses_anything_else(self):
        f, _ = self.fetch({"type": "dir", "sha": "0" * 40})
        with self.assertRaises(SystemExit):
            bs.pointer(f)


if __name__ == "__main__":
    unittest.main()
