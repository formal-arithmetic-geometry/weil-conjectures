"""Run the dispatcher's actual reaper without a live dispatcher or server."""
from pathlib import Path
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import dispatch_all


class NoAnswer(unittest.TestCase):
    def setUp(self):
        self.rate_limits = 0
        self.successes = 0
        for name, value in {"DRY": False, "alive": lambda pid: False,
                            "log": lambda *args: None,
                            "CAPACITY": SimpleNamespace(success=self.success,
                                                        rate_limited=self.rate_limited)}.items():
            patcher = patch.object(dispatch_all, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.item = "Sheaf.CategoryTheory.ModuleInverseImageAdjunction"
        self.key = self.item + "@"
        self.g = dispatch_all.Group.__new__(dispatch_all.Group)
        self.g.g = "B2"
        self.g.b = SimpleNamespace(sandbox=lambda stage: self.root)
        self.g.save = lambda: None
        self.g.st = {"stage": {self.item: "3"}, "tries": {self.key: 10}, "notes": {},
                     "running": {self.item: {"pid": 123, "last": str(self.root / "last.txt"),
                                            "t": time.time(), "kind": "repair", "key": self.key}}}

    def success(self):
        self.successes += 1

    def rate_limited(self):
        self.rate_limits += 1

    def reap(self, log="", answer=None):
        (self.root / "log.txt").write_text(log)
        if answer is not None:
            (self.root / "last.txt").write_text(answer)
        self.g.reap()
        self.assertNotIn(self.item, self.g.st["running"])
        return self.g.st["notes"].get(self.item, "")

    def test_missing_answer_keeps_http429_diagnosis_and_counts_failure(self):
        note = self.reap("ERROR: exceeded retry limit, last status: 429 Too Many Requests\n")
        self.assertTrue(note.startswith("PROVIDER_RATE_LIMIT:"))
        self.assertIn("429", note)
        self.assertIn("preserved sandbox", note)
        self.assertEqual(self.g.st["tries"][self.key], 11)
        self.assertEqual(self.rate_limits, 1)
        self.assertNotIn("blocked", self.g.st)

    def test_empty_answer_also_keeps_http429_diagnosis(self):
        self.assertIn("429", self.reap(
            "ERROR: exceeded retry limit, last status: 429 Too Many Requests\n", ""))

    def test_large_failure_count_does_not_block_or_release_item(self):
        self.g.st["tries"][self.key] = 10000
        self.reap("ERROR: exceeded retry limit, last status: 429 Too Many Requests\n")
        self.assertEqual(self.g.st["tries"][self.key], 10001)
        self.assertNotIn("blocked", self.g.st)
        self.assertNotIn("gaveup", self.g.st)

    def test_valid_final_answer_wins_over_old_transport_error(self):
        self.g.st["notes"][self.item] = "old failure"
        note = self.reap("ERROR: exceeded retry limit, last status: 429 Too Many Requests\n",
                         "DELIVERED " + self.item)
        self.assertEqual(note, "")
        self.assertEqual(self.g.st["tries"][self.key], 10)
        self.assertEqual(self.rate_limits, 0)
        self.assertEqual(self.successes, 1)

    def test_unrecognized_final_text_is_preserved(self):
        self.assertEqual(self.reap(answer="Unexpected result"), "NOANSWER: Unexpected result")

    def test_missing_log_is_reported_without_crashing(self):
        self.g.reap()
        self.assertTrue(self.g.st["notes"][self.item].startswith("NOANSWER:"))
        self.assertEqual(self.g.st["tries"][self.key], 11)
        self.assertEqual(self.rate_limits, 0)


if __name__ == "__main__":
    unittest.main()
