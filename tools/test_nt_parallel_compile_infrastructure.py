"""Exercise real landing decisions without loading the project or writing a return."""
import ast
import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest


source = Path(__file__).with_name('nt_parallel2.py')
if not source.exists():
    source = Path('/home/ubuntu/weil-newtargets/tools/nt_parallel2.py')
tree = ast.parse(source.read_text())
functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)
             and node.name in ('compile_infrastructure_failure', 'commit')]
namespace = {'re': re, 'json': json}
exec(compile(ast.Module(body=functions, type_ignores=[]), str(source), 'exec'), namespace)
classify = namespace['compile_infrastructure_failure']


class CompilerInfrastructure(unittest.TestCase):
    def test_original_q102_receipt(self):
        self.assertTrue(classify({
            'rc': 2, 'out': 'Extra data: line 21 column 2 (char 3020)'}))

    def test_json_exception_and_existing_infrastructure(self):
        self.assertTrue(classify({'rc': 2, 'out':
            "JSONDecodeError('Expecting value: line 1 column 1 (char 0)')"}))
        self.assertTrue(classify({'rc': 75, 'infra': True, 'out': 'stale live olean'}))

    def test_lean_errors_and_success_are_not_reclassified(self):
        for receipt in ({'rc': 1, 'out': 'Test.lean:1:0: error: type mismatch'},
                        {'rc': 1, 'out': 'Test.lean:1:0: error: Extra data'},
                        {'rc': 0, 'out': 'Extra data: line 21 column 2 (char 3020)'},
                        {'rc': 2, 'out': 'unknown failure'}, {}):
            with self.subTest(receipt=receipt):
                self.assertFalse(classify(receipt))

    def test_transaction_retries_json_error_without_returning_delivery(self):
        plan = {'id': 'plan', 'row': {'head': 'head'}}
        returns = []
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp)
            (state / 'plan.json').write_text(json.dumps(plan))
            namespace.update(STATE=state, do_return=lambda *args: returns.append(args))
            with contextlib.redirect_stdout(io.StringIO()):
                result = namespace['commit']([plan], {'plan': {
                    'id': 'plan', 'rc': 2,
                    'out': 'Extra data: line 21 column 2 (char 3020)'}}, None)
        self.assertEqual(returns, [])
        self.assertEqual(result['head']['result'], 'retry')
        self.assertTrue(result['head']['note'].startswith('INFRASTRUCTURE RETRY'))


if __name__ == '__main__':
    unittest.main()
