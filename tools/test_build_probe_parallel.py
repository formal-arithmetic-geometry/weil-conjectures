#!/usr/bin/env python3
"""The parallel probe fallback of tools/build.py (2026-10-20) runs with tools/ on sys.path, where tools/queue.py
shadows the stdlib `queue`: build.py imports concurrent.futures first. Run: python3 tools/test_build_probe_parallel.py"""
import pathlib, sys, unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import build  # noqa: E402


class T(unittest.TestCase):
    def test_parallel_probe_fallback(self):
        calls = []
        orig = build.run_probe
        def fake(mods, name="BatchProbe", threads=None):
            calls.append((tuple(mods), name))
            ran = len(mods) == 1
            return {m: {"ran": ran, "axioms": [], "sorry": [], "out": ""} for m in mods}
        build.run_probe = fake
        try:
            import concurrent.futures
            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
                out = list(ex.map(lambda m: build.run_probe([m], "BatchProbe_" + m)[m], ["A.B", "C.D", "E.F"]))
        finally:
            build.run_probe = orig
        self.assertTrue(all(r["ran"] for r in out))
        self.assertEqual(len(calls), 3)

    def test_queue_is_stdlib_for_executor(self):
        import queue
        self.assertTrue(hasattr(queue, "SimpleQueue"))


if __name__ == "__main__":
    unittest.main()
