"""Storage recovery must work without changing Lean sources or build stamps."""
import json
import pathlib
import tempfile
import time
import unittest
from unittest import mock

import nt_srv_compile as compiler


DISK_ERROR = "resource exhausted (error code: 28, no space left on device)\n[5.0 s]"


class StorageRecovery(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = pathlib.Path(self.tmp.name)
        self.src = root / "Probe.lean"
        self.src.write_text("module\n")
        self.cache = root / "cache"
        self.module = "Sheaf.Stage2.StorageProbe"
        self.base = self.cache / self.module
        self.base.mkdir(parents=True)
        self.failure = self.base / "key.fail"
        self.patches = [mock.patch.object(compiler, "KC", self.cache),
                        mock.patch.object(compiler, "key_of", return_value="key"),
                        mock.patch.object(compiler, "ORIGINAL_ARTS", return_value={})]
        for patch in self.patches:
            patch.start()
            self.addCleanup(patch.stop)
        compiler.CALL_START[0] = time.time()

    def compile(self):
        compiler.kcompile(self.module, self.src, "library", "overlay ", None, [])

    def test_old_and_concurrent_storage_failures_are_recompiled(self):
        for recorded in (time.time() - 120, time.time() + 1):
            with self.subTest(recorded=recorded):
                self.failure.write_text(json.dumps({"rc": 1, "out": DISK_ERROR, "t": recorded}))
                with mock.patch.object(compiler.lc, "run", return_value=(0, "Compiled")) as run:
                    self.compile()
                run.assert_called_once()
                self.assertFalse(self.failure.exists())
                (self.base / "key" / "result.json").unlink()
                (self.base / "key").rmdir()

    def test_new_storage_failure_is_not_persisted_or_blame_assigned(self):
        with mock.patch.object(compiler.lc, "run", return_value=(1, DISK_ERROR)):
            with self.assertRaises(compiler.CompileError):
                self.compile()
        self.assertFalse(self.failure.exists())
        self.assertFalse(compiler.FAILED_IN_DELIVERED[0])

    def test_real_lean_error_keeps_single_flight_failure_cache(self):
        error = "Probe.lean:1:0: error: type mismatch"
        self.failure.write_text(json.dumps({"rc": 1, "out": error, "t": time.time()}))
        with mock.patch.object(compiler.lc, "run") as run:
            with self.assertRaises(compiler.CompileError) as exc:
                self.compile()
        run.assert_not_called()
        self.assertIn(error, exc.exception.out)
        self.assertTrue(compiler.FAILED_IN_DELIVERED[0])

    def test_storage_errors_have_infrastructure_status(self):
        for error in (compiler.CompileError(1, DISK_ERROR), OSError(28, "No space left on device"),
                      OSError(122, "Disk quota exceeded")):
            with self.subTest(error=str(error)), \
                    mock.patch.object(compiler, "run", side_effect=error), \
                    mock.patch.object(compiler, "published", return_value=None), \
                    mock.patch.object(compiler, "stale_live_clash") as stale:
                compiler.FAILED_IN_DELIVERED[0] = True
                receipt = compiler.compile_plan({"id": "probe", "modules": [
                    {"file": "lean/Probe.lean", "text": "module\n"}]})
            self.assertEqual(receipt["rc"], compiler.INFRA_RC)
            self.assertTrue(receipt["infra"])
            self.assertIn("INFRASTRUCTURE RETRY (server storage)", receipt["out"])
            self.assertFalse(compiler.FAILED_IN_DELIVERED[0])
            stale.assert_not_called()


if __name__ == "__main__":
    unittest.main()
