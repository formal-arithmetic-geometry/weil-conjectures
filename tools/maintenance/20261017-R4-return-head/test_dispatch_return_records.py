"""Exercise real return scheduling without importing or starting the dispatcher."""
import ast
import os
from pathlib import Path
import re
from types import SimpleNamespace
import tempfile
import time
import unittest


source = Path(os.environ.get('DISPATCH_SOURCE',
                             Path(__file__).with_name('dispatch_all.py'))).read_text()
tree = ast.parse(source)
group = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'Group')
functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
             and n.name in ('parse_returns', 'noanswer_detail')]
work = next(n for n in group.body if isinstance(n, ast.FunctionDef) and n.name == 'work')
namespace = {'re': re, 'pathlib': __import__('pathlib'), 'os': os, 'time': time,
             'DRY': True, 'alive': lambda pid: False}
exec(compile(ast.Module(body=functions + [work], type_ignores=[]),
             '<dispatcher return records>', 'exec'), namespace)
parse_returns = namespace['parse_returns']
noanswer_detail = namespace['noanswer_detail']

ITEM = 'Sheaf.RingTheory.PopescuLiftChartFlat'
RETURN = f'## {ITEM} (2026-10-16T22:41:40Z, head 8ad217867)\n\nrepair upstream sync\n'


class ReturnRecords(unittest.TestCase):
    def test_both_return_producers(self):
        expected = {ITEM: ('8ad217867', 'repair upstream sync')}
        self.assertEqual(parse_returns(RETURN), expected)
        self.assertEqual(parse_returns(RETURN.replace(', head ', ', branch head ')), expected)

    def test_headless_legacy_return_and_notice(self):
        text = '- upstream sync notice\n\n## lem-example (2026-10-17)\n\nrepair\n'
        self.assertEqual(parse_returns(text), {'lem-example': ('', 'repair')})

    def scheduled(self, branch_head, failures=10000):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            batch = SimpleNamespace(skip={}, sandbox=lambda stage: root,
                                    not_ours=lambda *args: '')
            worker = SimpleNamespace(
                st={'running': {}, 'tries': {ITEM + '@8ad217867': failures},
                    'notes': {}, 'stage': {ITEM: '3'}}, b=batch, g='R4', clone=root,
                server=lambda: ([ITEM], {ITEM: branch_head}, parse_returns(RETURN)),
                adopt_shared=lambda: None, refresh=lambda: None,
                stage=lambda item: '3', maint=lambda *args: None)
            return namespace['work'](worker)

    def test_newer_delivery_waits_for_review(self):
        self.assertEqual(self.scheduled('885035f293384de456295e7fee0a6cc7f4ba6898'), [])

    def test_rejected_head_retries_regardless_of_failure_count(self):
        todo = self.scheduled('8ad217867a')
        self.assertEqual(len(todo), 1)
        self.assertEqual(todo[0][:4], ('3', ITEM, 'repair', ITEM + '@8ad217867'))

    def test_missing_answer_keeps_provider_diagnostic(self):
        with tempfile.TemporaryDirectory() as tmp:
            last = Path(tmp) / 'last.txt'
            last.with_name('log.txt').write_text(
                'worker output\nERROR: exceeded retry limit, last status: '
                '429 Too Many Requests, request id: example\ntokens used\n2\n')
            self.assertIn('429 Too Many Requests', noanswer_detail(last))
            self.assertIn('request id: example', noanswer_detail(last))

    def test_no_fabricated_diagnostic(self):
        with tempfile.TemporaryDirectory() as tmp:
            last = Path(tmp) / 'last.txt'
            self.assertEqual(noanswer_detail(last), '')
            last.with_name('log.txt').write_text('no fatal diagnostic\n')
            self.assertEqual(noanswer_detail(last), '')

    def test_runtime_uses_tested_functions(self):
        self.assertIn('ret = parse_returns(c)', source)
        self.assertIn('rest = noanswer_detail(lm)[:260]', source)


if __name__ == '__main__':
    unittest.main()
