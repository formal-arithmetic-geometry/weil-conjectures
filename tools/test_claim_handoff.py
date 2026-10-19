#!/usr/bin/env python3
"""Repair handoffs retain the rejected revision across later delivery pushes."""
import pathlib
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import claim


class RepairHandoffTest(unittest.TestCase):
    item = "lem-test-repair"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        self.git("init", "-q")
        # Create real commit objects and refs without modifying the live project.
        tree = self.git("mktree", input="")
        self.base = self.git("commit-tree", tree, input="returned snapshot\n")
        self.delivery = self.git("commit-tree", tree, "-p", self.base,
                                 input="repaired delivery\n")
        self.git("update-ref", "HEAD", self.base)
        self.branch = "refs/heads/deliver/Q43/" + self.item
        self.returns = self.root / "coord" / "returns"
        for patcher in (
            patch.object(claim.li, "ROOT", self.root),
            patch.object(claim, "RETURNS", self.returns),
            patch.object(claim, "repair_note", return_value={
                "state": "released", "note": "repair step 4", "reason": "split hidden lemmas"}),
            patch.object(claim, "commit_bookkeeping"),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)

    def git(self, *args, input=None):
        return subprocess.check_output(
            ["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", *args],
            cwd=self.root, input=input, text=True).strip()

    def handoff_head(self):
        text = (self.returns / "Q43.md").read_text()
        header = next(line for line in text.splitlines() if line.startswith("## "))
        self.assertIn("repair step 4", text)
        self.assertIn("split hidden lemmas", text)
        # This is the header syntax consumed by dispatch_all.parse_returns.
        return re.search(r"\bhead\s+([0-9a-f]{7,40})\b", header).group(1)

    def test_initial_handoff_uses_project_head(self):
        claim.handoff_return("Q43", self.item)
        returned = self.handoff_head()
        self.assertEqual(returned, self.base)
        self.git("update-ref", self.branch, self.delivery)
        self.assertFalse(self.git("rev-parse", self.branch).startswith(returned[:7]))

    def test_existing_delivery_stays_eligible_until_repushed(self):
        self.git("update-ref", self.branch, self.base)
        claim.handoff_return("Q43", self.item)
        returned = self.handoff_head()
        self.assertTrue(self.git("rev-parse", self.branch).startswith(returned[:7]))
        self.git("update-ref", self.branch, self.delivery)
        self.assertFalse(self.git("rev-parse", self.branch).startswith(returned[:7]))

    def test_existing_branch_is_used_instead_of_project_head(self):
        self.git("update-ref", self.branch, self.delivery)
        claim.handoff_return("Q43", self.item)
        self.assertEqual(self.handoff_head(), self.delivery)

    def test_abandon_archives_the_delivery_branch(self):
        # 2026-10-18: an abandoned item must become open again: its branch is archived and deleted.
        self.git("update-ref", self.branch, self.delivery)
        with patch.object(claim, "log"):
            self.assertEqual(claim.retire_delivery("Q43", self.item), self.delivery)
            self.assertIsNone(claim.retire_delivery("Q43", self.item))
        self.assertEqual(self.git("rev-parse", "refs/superseded/Q43/" + self.item + "/" + self.delivery), self.delivery)
        self.assertEqual(subprocess.run(["git", "rev-parse", "-q", "--verify", self.branch], cwd=self.root,
                                        capture_output=True).returncode, 1)

    def test_unreleased_note_creates_no_return(self):
        with patch.object(claim, "repair_note", return_value={"state": "done"}):
            claim.handoff_return("Q43", self.item)
        self.assertFalse((self.returns / "Q43.md").exists())


if __name__ == "__main__":
    unittest.main()
