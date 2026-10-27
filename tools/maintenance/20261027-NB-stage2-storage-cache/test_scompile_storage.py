"""The launcher must reject cached storage failures after server recovery."""
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, "/home/ubuntu/weil-launcher-all/batch2")
import scompile


class StorageResultCache(unittest.TestCase):
    def test_only_deterministic_results_are_reused(self):
        self.assertTrue(scompile.cacheable([0, "Compiled"]))
        self.assertTrue(scompile.cacheable([1, "Probe.lean:1:0: error: type mismatch"]))
        for result in ([1, "resource exhausted (error code: 28, no space left on device)"],
                       [2, "OSError(28, 'No space left on device')"],
                       [1, "Disk quota exceeded"], [75, "infrastructure failure"], [124, "timeout"]):
            with self.subTest(result=result):
                self.assertFalse(scompile.cacheable(result))

    def test_unchanged_request_rejects_preexisting_error_28_cache(self):
        stale = [1, "overlay AdicCohomologyTorsionNormalForm\n"
                    "resource exhausted (error code: 28, no space left on device)"]
        def attach(*args, valid, **kwargs):
            return stale if valid(stale) else [0, "Recovered"]

        with tempfile.TemporaryDirectory() as td:
            path = pathlib.Path(td) / "Probe.lean"
            path.write_text("module\n")
            with mock.patch.dict(scompile.os.environ, {}, clear=True), \
                    mock.patch.object(scompile.CA, "attach", side_effect=attach):
                result = scompile.run_many("NB", "storage-regression", [str(path)])
        self.assertEqual(result, (0, "Recovered"))


if __name__ == "__main__":
    unittest.main()
