"""Regression for unpublished dependency repairs with an unchanged publication.

Run: python3 test_source_cache.py /path/to/lcompile.py
Uses real git commits and the real attachment cache; no Lean or SSH calls.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


compiler_path = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(compiler_path.parent))
sys.path.append('/home/ubuntu/weil-launcher')
spec = importlib.util.spec_from_file_location('tested_lcompile', compiler_path)
compiler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compiler)
attach = compiler.CA


class SourceCacheTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.home = Path(self.temp.name)
        self.repo = self.home / 'weil-conjectures-sheaf-shared'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.name', 'Cache regression')
        self.git('config', 'user.email', 'cache@example.invalid')
        (self.repo / 'lean').mkdir()
        self.dependency = self.repo / 'lean/Dependency.lean'
        self.dependency.write_text('-- warning: unused simp argument\n')
        self.commit('initial')
        self.root = self.home / 'sandbox/lean'
        self.root.mkdir(parents=True)
        self.source = self.root / 'Consumer.lean'
        self.source.write_text('module\nimport Dependency\n')
        self.jobs = [(self.source, None, '')]
        compiler._SNAP[str(self.source)] = self.source.read_bytes()
        for context in (patch.object(compiler, 'H', self.home),
                        patch.object(attach, 'published_stamp', return_value='unchanged-publication')):
            context.start()
            self.addCleanup(context.stop)

    def git(self, *args):
        return subprocess.run(['git', *args], cwd=self.repo, check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, message):
        self.git('add', 'lean')
        self.git('commit', '-qm', message)

    def dep(self):
        return compiler._dep(self.jobs, self.root, None)

    def test_source_repair_invalidates_cached_warning(self):
        results = self.home / 'results'
        results.mkdir()
        runner = self.home / 'fixture.py'
        trace = self.home / 'runs'
        runner.write_text(
            'def run(args, sources):\n'
            f'    with open({str(trace)!r}, "a") as f: f.write("compiled\\n")\n'
            '    return [[0, "compiled repaired dependency"]]\n')
        specification = {'module': str(runner), 'module_name': 'source_cache_fixture',
                         'func': 'run', 'args': {}, 'label': 'source-cache-regression',
                         'fail_result': [[2, 'fixture runner failed']]}
        old_dep = self.dep()
        old_result = [[0, 'Compiled unpublished dependency Dependency\nwarning: unused simp argument']]
        (results / f'fixture-content-{old_dep}.json').write_text(json.dumps({'result': old_result}))
        with patch.object(attach, 'RES', results), patch.object(attach, 'LOG', self.home / 'attach.log'):
            def request():
                return attach.attach('fixture-', 'task', 'content', self.dep(), specification, {})
            self.assertEqual(request(), old_result)
            self.dependency.write_text('-- redundant simp argument removed\n')
            self.commit('repair dependency without publishing a build')
            repaired = request()
            self.assertEqual(repaired, [[0, 'compiled repaired dependency']])
            self.assertEqual(trace.read_text().splitlines(), ['compiled'])
            self.assertEqual(request(), repaired)
            self.assertEqual(trace.read_text().splitlines(), ['compiled'])

    def test_metadata_commit_preserves_cache(self):
        before = self.dep()
        (self.repo / 'coord').mkdir()
        (self.repo / 'coord/note.md').write_text('unrelated bookkeeping\n')
        self.git('add', 'coord/note.md')
        self.git('commit', '-qm', 'metadata only')
        self.assertEqual(self.dep(), before)

    def test_unavailable_source_snapshot_does_not_reuse_cache(self):
        self.git('update-ref', '-d', 'HEAD')
        self.assertNotEqual(self.dep(), self.dep())


if __name__ == '__main__':
    unittest.main()
