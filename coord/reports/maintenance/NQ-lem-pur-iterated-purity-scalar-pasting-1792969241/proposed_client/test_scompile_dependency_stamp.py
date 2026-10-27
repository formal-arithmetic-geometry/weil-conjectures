"""Regression checks for source repairs during an unchanged published build."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import scompile


class DependencyStampTests(unittest.TestCase):
    def setUp(self):
        self.env = patch.dict(os.environ)
        self.env.start()
        os.environ.pop(scompile.CA.DIRECT, None)
        self.temp = tempfile.TemporaryDirectory()
        self.source = Path(self.temp.name) / "lean/Sheaf/Paper/CacheProbe.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("module\n")

    def tearDown(self):
        self.temp.cleanup()
        self.env.stop()

    def test_committed_dependency_repair_invalidates_unchanged_worker_sources(self):
        with patch.object(scompile, "server_dependency_stamp",
                          side_effect=["published A; source A", "published A; source A",
                                       "published A; source B"]), \
                patch.object(scompile.CA, "attach", return_value=[0, "checked"]) as attach:
            for _ in range(3):
                self.assertEqual(scompile.run_many("NQ", "item", [self.source]), (0, "checked"))
        first, same, repaired = [call.args for call in attach.call_args_list]
        self.assertEqual(first[1:4], same[1:4])
        self.assertEqual(first[1], repaired[1])  # Still the same logical task.
        self.assertNotEqual(first[2], repaired[2])  # An old runner cannot satisfy it.
        self.assertNotEqual(first[3], repaired[3])  # Nor can an old stored result.

    def test_unavailable_state_does_not_reuse_a_cached_failure(self):
        with patch.object(scompile, "server_dependency_stamp", return_value=None), \
                patch.object(scompile.CA, "attach") as attach:
            rc, out = scompile.run_many("NQ", "item", [self.source])
        self.assertEqual(rc, 2)
        self.assertIn("no cached compile result reused", out)
        attach.assert_not_called()

    def test_state_covers_server_sources_tools_and_build_selection(self):
        result = subprocess.CompletedProcess([], 0, "source-tree\ntool-tree\nbuild-stamps\n", "")
        with patch.object(scompile.subprocess, "run", return_value=result) as run, \
                patch.object(scompile, "PROJECT", "/tmp/project with spaces"):
            self.assertEqual(scompile.server_dependency_stamp(), result.stdout.strip())
        command = run.call_args.args[0][-1]
        self.assertIn("cd '/tmp/project with spaces'", command)
        self.assertIn("HEAD:lean HEAD:tools", command)
        self.assertIn("local/builds/published.json", command)
        self.assertIn("local/builds/last.json", command)

    def test_failed_or_timed_out_state_is_not_a_stamp(self):
        with patch.object(scompile.subprocess, "run",
                          return_value=subprocess.CompletedProcess([], 1, "partial", "error")):
            self.assertIsNone(scompile.server_dependency_stamp())
        with patch.object(scompile.subprocess, "run",
                          side_effect=subprocess.TimeoutExpired("ssh", 30)):
            self.assertIsNone(scompile.server_dependency_stamp())


if __name__ == "__main__":
    unittest.main()
