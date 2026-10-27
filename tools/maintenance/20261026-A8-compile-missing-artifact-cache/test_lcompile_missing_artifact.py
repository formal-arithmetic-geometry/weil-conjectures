"""Exercise the real attachment cache with an isolated runner and no Lean/server calls.

Run: python3 test_lcompile_missing_artifact.py /path/to/lcompile.py
"""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


compiler_path = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(compiler_path.parent))
spec = importlib.util.spec_from_file_location("tested_lcompile", compiler_path)
compiler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compiler)
attach = compiler.CA


class MissingArtifactCacheTest(unittest.TestCase):
    def test_classification(self):
        for name in ("Subobject", "Etale", "FaithfullyFlatDescent"):
            result = [[1, f"Foo.lean:6:0: error: object file '/build/{name}.olean' "
                        f"of module WeilConjectures.{name} does not exist\n\n[60.0 s]"]]
            self.assertFalse(compiler.cacheable(result))
        self.assertFalse(compiler.cacheable([[124, "timeout"]]))
        self.assertTrue(compiler.cacheable([[0, "compiled"]]))
        self.assertTrue(compiler.cacheable([[1, "Foo.lean:9:2: error: Type mismatch"]]))

    def test_recovery_and_retained_results(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            root = directory / "lean"
            root.mkdir()
            source = root / "Example.lean"
            source.write_text("module\n")
            lb = directory / ".lbuild"
            lb.mkdir()
            results = directory / "results"
            results.mkdir()
            trace = directory / "runs"
            state = directory / "state.json"
            runner = directory / "runner.py"
            runner.write_text(
                "import importlib.util, json, pathlib, sys\n"
                f"sys.path.insert(0, {str(compiler_path.parent)!r})\n"
                f"s = importlib.util.spec_from_file_location('lcompile', {str(compiler_path)!r})\n"
                "m = importlib.util.module_from_spec(s); s.loader.exec_module(m)\n"
                "cacheable = m.cacheable\n"
                "def run(args, sources):\n"
                f"    with open({str(trace)!r}, 'a') as f: f.write('run\\n')\n"
                f"    return json.loads(pathlib.Path({str(state)!r}).read_text())\n"
            )
            real_attach = attach.attach
            cached = directory / "cache-path"

            def isolated_attach(kind, task, content, dep, specification, sources, **kwargs):
                ck = kind + content
                cache = results / f"{ck}-{dep}.json"
                cached.write_text(str(cache))
                if not cache.exists() and not trace.exists():
                    cache.write_text(json.dumps({"result": [[1,
                        "error: object file '/build/Subobject.olean' of module "
                        "WeilConjectures.Subobject does not exist"]]}))
                specification = dict(specification, module=str(runner),
                                     module_name="cache_fixture", func="run")
                return real_attach(kind, task, content, dep, specification, sources, **kwargs)

            jobs = [(source, None, "")]
            compiler._SNAP[str(source)] = source.read_bytes()
            with patch.object(attach, "RES", results), \
                    patch.object(attach, "LOG", directory / "attach.log"), \
                    patch.object(attach, "attach", isolated_attach):
                # Same source and publication: a cached artifact failure must run again.
                state.write_text(json.dumps([[0, "compiled after restoration"]]))
                first = compiler._attached(jobs, root, lb, 60, True)
                self.assertEqual(first, [(0, "compiled after restoration")])
                self.assertEqual(trace.read_text().splitlines(), ["run"])
                # A successful result stays reusable without another runner.
                self.assertEqual(compiler._attached(jobs, root, lb, 60, True), first)
                self.assertEqual(trace.read_text().splitlines(), ["run"])
                cache = Path(cached.read_text())
                cache.unlink()
                # A fresh artifact failure reaches the caller but is not stored.
                state.write_text(json.dumps([[1, "error: object file '/build/Etale.olean' "
                                             "of module WeilConjectures.Etale does not exist"]]))
                self.assertEqual(compiler._attached(jobs, root, lb, 60, True)[0][0], 1)
                self.assertFalse(cache.exists())
                # Ordinary Lean errors still cache; the environment error does not poison this call.
                state.write_text(json.dumps([[1, "error: Type mismatch"]]))
                failed = compiler._attached(jobs, root, lb, 60, True)
                self.assertEqual(failed, [(1, "error: Type mismatch")])
                self.assertTrue(cache.exists())
                self.assertEqual(compiler._attached(jobs, root, lb, 60, True), failed)
                self.assertEqual(len(trace.read_text().splitlines()), 3)


if __name__ == "__main__":
    unittest.main()
