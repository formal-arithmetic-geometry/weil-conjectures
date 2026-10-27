"""Exercise the duplicate gate with arXiv sources and real Stacks collisions."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest


TOOL = Path(os.environ.get(
    "STAGE1_DELIVERY_TOOL", "/home/ubuntu/weil-launcher-all/batch2/deliver.py"))
spec = importlib.util.spec_from_file_location("stage1_delivery_under_test", TOOL)
delivery = importlib.util.module_from_spec(spec)
spec.loader.exec_module(delivery)


class SourceTags(unittest.TestCase):
    def check_sources(self, source, existing_source=None, report=""):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            clone, sandbox = root / "clone", root / "sandbox"
            for directory in (clone, sandbox):
                (directory / "dag/nodes/chapter").mkdir(parents=True)
            item = {"id": "item", "source": source, "proof": [
                {"uses": ["helper"], "elementary": False},
                {"uses": [], "elementary": True},
            ]}
            helper = {"id": "helper", "source": source}
            files = []
            for node in (item, helper):
                path = sandbox / "dag/nodes/chapter" / (node["id"] + ".json")
                path.write_text(json.dumps(node))
                files.append(path)
            (clone / "dag/nodes/chapter/item.json").write_text(json.dumps(item))
            if existing_source:
                (clone / "dag/nodes/chapter/existing.json").write_text(json.dumps(
                    {"id": "existing", "source": existing_source}))
            rep = sandbox / "report.md"
            rep.write_text(report)
            return delivery.dup_check(clone, sandbox, "item", files, rep)

    def test_morrison_arxiv_source_does_not_trigger_d1_d2(self):
        source = {
            "document": "literature/morrison-git-stable-curves-arXiv-0810.2340.pdf",
            "place": "Section 2.4, Lemma 6; https://arxiv.org/pdf/0810.2340.",
            "url": "https://arxiv.org/pdf/0810.2340",
        }
        self.assertEqual(self.check_sources(source), [])

    def test_arxiv_does_not_collide_with_real_numeric_stacks_tag(self):
        source = {"document": "arXiv:0810.2340"}
        stacks = {"document": "Stacks Project", "place": "Tag 0810"}
        self.assertEqual(self.check_sources(source, stacks), [])

    def test_arxiv_identifier_forms_and_revisions(self):
        for reference in ("0810.2340", "0810.2340v2", "arXiv:0810.2340",
                          "arXiv-0810.2340.pdf", "https://arxiv.org/abs/0810.2340",
                          "https://arxiv.org/pdf/0810.2340v12.pdf",
                          "arXiv:0810.12345v3", "arXiv:0701.0001"):
            with self.subTest(reference=reference):
                self.assertEqual(self.check_sources({"document": reference}), [])

    def test_real_numeric_stacks_tag_still_blocks(self):
        bad = self.check_sources({"document": "Stacks Project", "place": "Tag 0810"})
        self.assertTrue(any("D1, D2" in message for message in bad))
        self.assertTrue(any("item (0810)" in message for message in bad))

    def test_real_alphabetic_stacks_tag_still_blocks(self):
        bad = self.check_sources({"document": "literature/stacks-project/algebra.tex",
                                  "place": "Lemma 00PD"})
        self.assertTrue(any("D1, D2" in message for message in bad))

    def test_stacks_url_still_blocks(self):
        bad = self.check_sources({"url": "https://stacks.math.columbia.edu/tag/0810"})
        self.assertTrue(any("D1, D2" in message for message in bad))

    def test_real_tag_alongside_arxiv_is_retained(self):
        for tag in ("0810", "00PD"):
            with self.subTest(tag=tag):
                bad = self.check_sources({"document": "arXiv:0810.2340",
                                          "place": "Also Stacks Tag " + tag})
                self.assertTrue(any("D1, D2" in message for message in bad))
                self.assertTrue(any("item (" + tag + ")" in message for message in bad))

    def test_duplicate_report_does_not_bypass_real_d1_d2(self):
        bad = self.check_sources({"document": "Stacks Project", "place": "Tag 0810"},
                                 report="## Not duplicates\nhelper vs item: different claims\n")
        self.assertEqual(len(bad), 1)
        self.assertIn("D1, D2", bad[0])


if __name__ == "__main__":
    unittest.main()
