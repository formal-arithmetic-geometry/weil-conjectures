"""A later timeout must retain diagnostics already emitted by Lean.

These tests replace only the Lean subprocess, so no build or compile limit changes.
"""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import nt_compile
import nt_lcompile


class TimeoutDiagnostics(unittest.TestCase):
    outputs = ((b"Earlier.lean:2:0: error: bad type\n", b"profiler: slow definition\n"),
               ("Earlier.lean:2:0: error: bad type", "profiler: slow definition"),
               (None, None), (b"invalid UTF-8: \xff", None))

    def assert_diagnostics(self, text, stdout, stderr):
        for value in (stdout, stderr):
            if value:
                expected = value.decode(errors="replace") if isinstance(value, bytes) else value
                self.assertIn(expected, text)
        self.assertIn("timeout after 60 s", text)

    def test_overlay_backend_retains_partial_output_and_releases_slot(self):
        for stdout, stderr in self.outputs:
            with self.subTest(stdout=stdout, stderr=stderr), tempfile.TemporaryDirectory() as td:
                root = Path(td) / "lean"
                root.mkdir()
                src = root / "TimedOut.lean"
                src.write_text("module\n")
                slot = mock.Mock()
                expired = subprocess.TimeoutExpired(["lean"], 60, output=stdout, stderr=stderr)
                with mock.patch.object(nt_lcompile, "base_opts", return_value=[]), \
                        mock.patch.object(nt_lcompile, "local_artifacts", return_value={}), \
                        mock.patch.object(nt_lcompile, "take_slot", return_value=slot), \
                        mock.patch.object(nt_lcompile.fcntl, "flock") as unlock, \
                        mock.patch.object(nt_lcompile.subprocess, "run", side_effect=expired) as run:
                    rc, text = nt_lcompile.run(src)
                self.assertEqual(rc, 124)
                self.assert_diagnostics(text, stdout, stderr)
                self.assertEqual(run.call_args.kwargs["timeout"], 60)
                unlock.assert_called_once_with(slot, nt_lcompile.fcntl.LOCK_UN)
                slot.close.assert_called_once()

    def test_single_file_backend_retains_partial_output_without_caching_failure(self):
        for stdout, stderr in self.outputs:
            with self.subTest(stdout=stdout, stderr=stderr), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                live = root / "live"
                (live / ".lake/build/lib/lean").mkdir(parents=True)
                (live / "lakefile.toml").write_text("[leanOptions]\n")
                request = io.StringIO(json.dumps({"files": {"Sheaf/Stage2/TimedOut.lean": "module\n"}}))
                output = io.StringIO()
                expired = subprocess.TimeoutExpired(["lean"], 60, output=stdout, stderr=stderr)
                with mock.patch.object(nt_compile, "LIVE", live), \
                        mock.patch.object(nt_compile, "ROOT", root), \
                        mock.patch.object(nt_compile, "load_overrides", return_value=[]), \
                        mock.patch.object(nt_compile.os, "nice"), \
                        mock.patch.object(nt_compile.subprocess, "run", side_effect=expired) as run, \
                        mock.patch.object(sys, "argv", ["nt_compile.py", "--json"]), \
                        mock.patch.object(sys, "stdin", request), \
                        contextlib.redirect_stdout(output), \
                        self.assertRaises(SystemExit) as raised:
                    nt_compile.main()
                text = output.getvalue() + str(raised.exception)
                self.assert_diagnostics(text, stdout, stderr)
                self.assertEqual(run.call_args.kwargs["timeout"], 60)
                self.assertNotEqual(raised.exception.code, 0)


if __name__ == "__main__":
    unittest.main()
