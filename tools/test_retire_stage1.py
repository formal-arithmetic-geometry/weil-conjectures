"""Exercise superseded packet retirement in temporary git repositories."""
import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import retire_stage1 as retirement


class RetirementTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.addCleanup(patch.stopall)
        patch.object(retirement, "ROOT", self.root).start()
        self.item = "lem-completed"
        self.node = "dag/nodes/test/lem-completed.json"
        self.ret = "coord/returns/NN.md"
        self.claim = "coord/claims/lem-completed.lock"
        self.branch = "refs/heads/deliver/NN/lem-completed"
        self.git("init", "-q", "-b", "sheaf-dag")
        self.write(self.node, json.dumps({"id": self.item, "status": "split", "reviewed": {"group": "NP"}}))
        self.write(self.ret, "Notice\n\n## lem-other (today)\n\nKeep this.\n\n## lem-completed (today)\n\nRebase.\n")
        self.write(self.claim, json.dumps({"who": "NN"}))
        self.write("coord/ledger.md", "Ledger\n")
        self.write("coord/deliveries.log", "Deliveries\n")
        self.write("coord/queue.tsv", "")
        self.git("add", ".")
        self.git("commit", "-qm", "initial")
        self.head = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("update-ref", self.branch, self.head)

    def git(self, *args, check=True):
        return subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com", *args],
                              cwd=self.root, text=True, capture_output=True, check=check)

    def write(self, path, value):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(value)

    def retire(self):
        return retirement.retire_completed("NN", self.item, self.head)

    def test_completed_packet_is_archived_and_return_and_claim_closed(self):
        original = (self.root / self.node).read_bytes()
        self.assertTrue(self.retire())
        archive = f"refs/superseded/NN/{self.item}/{self.head}"
        self.assertEqual(self.git("rev-parse", archive).stdout.strip(), self.head)
        self.assertNotEqual(self.git("rev-parse", "--verify", self.branch, check=False).returncode, 0)
        self.assertFalse((self.root / self.claim).exists())
        text = (self.root / self.ret).read_text()
        self.assertIn("## lem-other (", text)
        self.assertNotIn("## lem-completed (", text)
        self.assertEqual((self.root / self.node).read_bytes(), original)
        self.assertEqual(len(list(self.root.rglob("*.bak"))), 4)
        self.assertIn("superseded", (self.root / "coord/deliveries.log").read_text())
        committed = self.git("rev-parse", "HEAD").stdout
        self.assertTrue(self.retire())  # exact archived retry is idempotent
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, committed)

    def test_sync_archived_packet_still_has_its_stale_return_retired(self):
        self.write(self.ret, f"Notice\n\n## {self.item} (today, branch head {self.head[:10]})\n\nRebase.\n")
        (self.root / self.claim).unlink()
        self.git("commit", "-qam", "sync removed claim but left return")
        self.git("update-ref", f"refs/superseded/NN/{self.item}/{self.head}", self.head)
        self.git("update-ref", "-d", self.branch, self.head)
        self.assertTrue(self.retire())
        self.assertNotIn("## lem-completed (", (self.root / self.ret).read_text())

    def test_sync_archive_does_not_remove_a_return_for_a_newer_head(self):
        self.write(self.ret, f"## {self.item} (today, branch head {'f' * 10})\n\nNew repair.\n")
        (self.root / self.claim).unlink()
        self.git("commit", "-qam", "newer return")
        self.git("update-ref", f"refs/superseded/NN/{self.item}/{self.head}", self.head)
        self.git("update-ref", "-d", self.branch, self.head)
        self.assertTrue(self.retire())
        self.assertIn("New repair", (self.root / self.ret).read_text())

    def test_unsplit_node_is_not_retired(self):
        self.write(self.node, json.dumps({"id": self.item, "status": "unsplit"}))
        self.git("commit", "-qam", "reopen")
        self.assertFalse(self.retire())
        self.assertTrue((self.root / self.claim).exists())

    def test_new_head_is_never_deleted(self):
        self.write("replacement", "new packet")
        self.git("add", "replacement")
        self.git("commit", "-qm", "replacement")
        replacement = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("update-ref", self.branch, replacement)
        with self.assertRaisesRegex(retirement.RetirementError, "HEAD MOVED"):
            self.retire()
        self.assertEqual(self.git("rev-parse", self.branch).stdout.strip(), replacement)
        self.assertTrue((self.root / self.claim).exists())

    def test_stage2_lean_delivery_is_preserved(self):
        self.git("checkout", "-qb", "packet")
        self.write("lean/Test.lean", "-- a stage-2 packet\n")
        self.git("add", "lean")
        self.git("commit", "-qm", "statement")
        self.head = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("update-ref", self.branch, self.head)
        self.git("checkout", "-q", "sheaf-dag")
        self.assertFalse(self.retire())
        self.assertTrue((self.root / self.claim).exists())

    def test_stage2_claim_survives_retirement_of_older_stage1_packet(self):
        self.write("coord/queue.tsv", self.item + "\t2\n")
        self.git("commit", "-qam", "stage 2 queued")
        self.assertTrue(self.retire())
        self.assertTrue((self.root / self.claim).exists())

    def test_other_groups_claim_is_preserved(self):
        self.write(self.claim, json.dumps({"who": "Q07"}))
        self.git("commit", "-qam", "next group")
        self.assertTrue(self.retire())
        self.assertEqual(json.loads((self.root / self.claim).read_text())["who"], "Q07")

    def test_commit_failure_restores_bookkeeping_and_preserves_branch(self):
        original = {p: (self.root / p).read_bytes() for p in (self.ret, self.claim, "coord/ledger.md", "coord/deliveries.log")}
        hook = self.root / ".git/hooks/pre-commit"
        hook.write_text("#!/bin/sh\nexit 1\n")
        hook.chmod(0o755)
        with self.assertRaises(retirement.RetirementError):
            self.retire()
        for path, data in original.items():
            self.assertEqual((self.root / path).read_bytes(), data)
        self.assertEqual(self.git("rev-parse", self.branch).stdout.strip(), self.head)

    def test_dirty_bookkeeping_is_not_committed(self):
        with (self.root / self.ret).open("a") as stream:
            stream.write("Someone else's change\n")
        with self.assertRaisesRegex(retirement.RetirementError, "uncommitted bookkeeping"):
            self.retire()
        self.assertTrue((self.root / self.claim).exists())

    def test_unrelated_staged_change_is_excluded_from_retirement_commit(self):
        self.write("unrelated", "keep staged\n")
        self.git("add", "unrelated")
        self.assertTrue(self.retire())
        self.assertEqual(self.git("diff", "--cached", "--name-only").stdout.strip(), "unrelated")
        self.assertNotIn("unrelated", self.git("show", "--format=", "--name-only", "HEAD").stdout)

    def test_concurrent_push_after_commit_is_preserved(self):
        self.write("replacement", "new packet")
        self.git("add", "replacement")
        self.git("commit", "-qm", "replacement")
        replacement = self.git("rev-parse", "HEAD").stdout.strip()
        real_run = subprocess.run

        def push_before_delete(args, **kwargs):
            if args[:3] == ["git", "update-ref", "--stdin"]:
                real_run(["git", "update-ref", self.branch, replacement], cwd=self.root, check=True)
            return real_run(args, **kwargs)

        with patch.object(retirement.subprocess, "run", side_effect=push_before_delete):
            with self.assertRaisesRegex(retirement.RetirementError, "HEAD MOVED during retirement"):
                self.retire()
        self.assertEqual(self.git("rev-parse", self.branch).stdout.strip(), replacement)


if __name__ == "__main__":
    unittest.main()
