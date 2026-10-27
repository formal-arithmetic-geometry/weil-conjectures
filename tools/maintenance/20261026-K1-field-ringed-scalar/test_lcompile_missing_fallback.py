"""Test the real local-service response path without Lean, SSH or published artifacts.

Run: python3 test_lcompile_missing_fallback.py /path/to/lcompile.py
"""
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

compiler_path = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(compiler_path.parent))
# A standalone patched copy still uses the launcher's attachment service.
sys.path.append('/home/ubuntu/weil-launcher')
spec = importlib.util.spec_from_file_location('tested_lcompile', compiler_path)
compiler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compiler)


class LocalMissingFallback(unittest.TestCase):
    def response(self, rc, diagnostic):
        with tempfile.TemporaryDirectory(prefix='K1-local-missing-test-') as directory:
            root = Path(directory)
            source = root / 'Example.lean'
            source.write_text('module\nimport Sheaf.Required\n')
            data = json.dumps({'td': '/service/scratch', 'results': [{
                'rel': 'Example.lean', 'rc': rc, 'out': diagnostic,
                'secs': 0.9, 'arts': False}]}).encode()
            reply = io.BytesIO()
            with tarfile.open(fileobj=reply, mode='w:gz') as archive:
                member = tarfile.TarInfo('result.json')
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
            process = subprocess.CompletedProcess([], 0, reply.getvalue(), b'')
            with patch.object(compiler.subprocess, 'run', return_value=process), \
                    patch.object(compiler, '_log'):
                return compiler._remote_jobs([(source, None, '')], root, None, 60,
                                             False, local=True)

    def test_lean_missing_object_goes_to_server(self):
        self.assertIsNone(self.response(1, "Example.lean:1:0: error: object file "
            "'/mirror/Sheaf/Paper/WeilTensorProduct.olean' of module "
            "Sheaf.Paper.WeilTensorProduct does not exist\n"))

    def test_failed_to_open_object_still_goes_to_server(self):
        self.assertIsNone(self.response(1, "failed to open file '/mirror/Required.olean'"))

    def test_local_service_failure_still_goes_to_server(self):
        self.assertIsNone(self.response(1, 'lset.py: local service failed'))

    def test_ordinary_lean_error_remains_an_answer(self):
        result = self.response(1, 'Example.lean:9:2: error: Type mismatch')
        self.assertEqual(result[0][0], 1)
        self.assertIn('Type mismatch', result[0][1])

    def test_success_remains_an_answer(self):
        self.assertEqual(self.response(0, '')[0][0], 0)


if __name__ == '__main__':
    unittest.main()
