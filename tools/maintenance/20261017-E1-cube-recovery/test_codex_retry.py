"""Provider failure regressions using real fake-CLI children, no model requests."""
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import codex_retry as retry


SID = "01a14716-9aa0-7193-af70-4bb9c50e6016"
FAKE = r'''#!/usr/bin/env python3
import json, os, pathlib, sys, time
args = sys.argv[1:]
log = pathlib.Path(os.environ['FAKE_LOG'])
entries = json.loads(log.read_text()) if log.exists() else []
entries.append({'args': args, 'stdin': sys.stdin.read(), 'cwd': os.getcwd()})
log.write_text(json.dumps(entries))
last = pathlib.Path(args[args.index('-o') + 1])
mode = os.environ['FAKE_MODE']
if mode != 'no-session':
    print('session id: 01a14716-9aa0-7193-af70-4bb9c50e6016', flush=True)
if mode == 'hang':
    print('ERROR: exceeded retry limit, last status: 429 Too Many Requests', flush=True)
    time.sleep(30)
elif mode == 'auth':
    print('ERROR: authentication failed: 401 Unauthorized', flush=True)
elif mode == 'quota':
    print('ERROR: 429 insufficient_quota', flush=True)
elif mode == 'concurrency':
    print('ERROR: stream disconnected before completion: Concurrency limit exceeded for account, please retry later', flush=True)
elif mode == 'exit-zero':
    sys.exit(0)
elif mode == 'final' or mode == 'recover' and len(entries) > 1:
    print('ERROR: Reconnecting after 429 Too Many Requests', flush=True)
    last.write_text('READY item: sandbox checked\n')
    sys.exit(0)
else:
    print('ERROR: exceeded retry limit, last status: 429 Too Many Requests, request id: abc', flush=True)
sys.exit(1)
'''


class WorkerRecovery(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.last = self.root / 'run/NK/item.123/last.txt'
        self.last.parent.mkdir(parents=True)
        self.fake = self.root / 'fake-codex'
        self.fake.write_text(FAKE)
        self.fake.chmod(0o755)
        self.log = self.root / 'calls.json'
        self.args = ['exec', '-c', 'model_providers.OpenAI.request_max_retries=30',
                     '-m', 'gpt-6.1-sol', '--skip-git-repo-check',
                     '--dangerously-bypass-approvals-and-sandbox',
                     '-C', str(self.root), '-o', str(self.last), '-']
        self.sleeps = []
        self.output = io.StringIO()

    def run_fake(self, mode, **kwargs):
        env = {'FAKE_LOG': str(self.log), 'FAKE_MODE': mode}
        with patch.dict(os.environ, env), patch('sys.stdin', io.StringIO('original brief\n')):
            rc = retry.supervise(self.args, self.last, self.fake, sleep=self.sleeps.append,
                                 emit=self.output.write, **kwargs)
        return rc, json.loads(self.log.read_text())

    def state(self):
        return json.loads(self.last.with_name('codex-retry.json').read_text())

    def test_mid_work_rate_limit_resumes_exact_session_with_original_flags(self):
        rc, calls = self.run_fake('recover', delay=lambda n: 31)
        self.assertEqual(rc, 0)
        self.assertEqual(calls[0]['stdin'], 'original brief\n')
        resumed = calls[1]['args']
        self.assertEqual(resumed[:2], ['exec', 'resume'])
        self.assertEqual(resumed[-2:], [SID, '-'])
        self.assertNotIn('-C', resumed)
        self.assertIn('gpt-6.1-sol', resumed)
        self.assertIn('model_providers.OpenAI.request_max_retries=30', resumed)
        self.assertEqual(calls[0]['cwd'], calls[1]['cwd'])
        self.assertIn('check any interrupted tool', calls[1]['stdin'])
        self.assertEqual(self.sleeps, [30, 1])
        self.assertEqual(self.last.read_text(), 'READY item: sandbox checked\n')
        self.assertEqual(self.state()['status'], 'answered')

    def test_startup_rate_limit_retries_original_brief_without_session(self):
        rc, calls = self.run_fake('no-session', max_recoveries=1, delay=lambda n: 0)
        self.assertEqual(rc, 1)
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0], calls[1])
        self.assertTrue(self.last.read_text().startswith('BLOCKED item: provider HTTP 429'))

    def test_explicit_dispatcher_resume_recovers_without_duplicate_positionals(self):
        self.args = retry.resume_args(self.args, SID)
        self.assertEqual(retry.output_path(self.args, self.root / 'run'), self.last)
        rc, calls = self.run_fake('recover', delay=lambda n: 0)
        self.assertEqual(rc, 0)
        self.assertEqual(len(calls), 2)
        for call in calls:
            self.assertEqual(call['args'][:2], ['exec', 'resume'])
            self.assertEqual(call['args'].count('resume'), 1)
            self.assertEqual(call['args'].count(SID), 1)
            self.assertEqual(call['args'][-2:], [SID, '-'])
            self.assertNotIn('-C', call['args'])
            self.assertIn('gpt-6.1-sol', call['args'])
        self.assertEqual(self.state()['status'], 'answered')

    def test_resume_startup_failure_keeps_requested_session_without_header(self):
        self.args = retry.resume_args(self.args, SID)
        rc, calls = self.run_fake('no-session', max_recoveries=1, delay=lambda n: 0)
        self.assertEqual(rc, 1)
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0]['args'], calls[1]['args'])
        self.assertEqual(calls[1]['args'][-2:], [SID, '-'])
        self.assertEqual(self.state()['session_id'], SID)

    def test_resume_replaces_old_session_when_cli_reports_a_new_id(self):
        previous = '01a14742-d37b-7cb1-8eeb-be9040c121b1'
        self.args = retry.resume_args(self.args, previous)
        rc, calls = self.run_fake('recover', delay=lambda n: 0)
        self.assertEqual(rc, 0)
        self.assertIn(previous, calls[0]['args'])
        self.assertNotIn(previous, calls[1]['args'])
        self.assertEqual(calls[1]['args'][-2:], [SID, '-'])

    def test_exhaustion_keeps_diagnostic_and_no_fake_success(self):
        rc, calls = self.run_fake('exhaust', max_recoveries=2, delay=lambda n: 0)
        self.assertEqual(rc, 1)
        self.assertEqual(len(calls), 3)
        self.assertIn('retry limit', self.last.read_text())
        self.assertIn('request id: abc', self.last.read_text())
        self.assertEqual(self.state()['recoveries'], 2)

    def test_worker_deadline_bounds_retries(self):
        rc, calls = self.run_fake('exhaust', budget=10, delay=lambda n: 30)
        self.assertEqual(len(calls), 1)
        self.assertIn('worker budget', self.last.read_text())
        self.assertEqual(self.sleeps, [])

    def test_provider_concurrency_error_has_the_same_recovery(self):
        rc, calls = self.run_fake('concurrency', max_recoveries=1, delay=lambda n: 0)
        self.assertEqual(len(calls), 2)
        self.assertEqual(rc, 1)
        self.assertIn('Concurrency limit exceeded', self.last.read_text())

    def test_authentication_and_quota_failures_do_not_retry(self):
        for mode in ['auth', 'quota']:
            with self.subTest(mode=mode):
                self.log.unlink(missing_ok=True)
                rc, calls = self.run_fake(mode, delay=lambda n: 0)
                self.assertEqual(rc, 1)
                self.assertEqual(len(calls), 1)
                self.assertFalse(self.last.exists())

    def test_real_answer_wins_over_prior_rate_limit(self):
        rc, calls = self.run_fake('final', delay=lambda n: 0)
        self.assertEqual(len(calls), 1)
        self.assertEqual(rc, 0)
        self.assertEqual(self.last.read_text(), 'READY item: sandbox checked\n')

    def test_zero_exit_without_answer_is_not_retried(self):
        rc, calls = self.run_fake('exit-zero', delay=lambda n: 0)
        self.assertEqual(len(calls), 1)
        self.assertEqual(rc, 0)
        self.assertFalse(self.last.exists())

    def test_only_dispatcher_worker_invocations_are_managed(self):
        root = self.root / 'run'
        self.assertEqual(retry.output_path(self.args, root), self.last)
        for args in [['--version'], ['exec', '-o', '/tmp/last.txt', '-'],
                     ['exec', '--json', '-o', str(self.last), '-'],
                     ['exec', 'resume', '-o', str(self.last), '--last', '-'],
                     ['exec', 'resume', '-o', str(self.last), 'unknown-session', '-'],
                     ['exec', 'resume', '-o', str(self.last), '-'],
                     ['exec', 'resume', '--last', '-o', str(self.last), SID, '-'],
                     ['exec', '-o', str(root / '../other/a/last.txt'), '-']]:
            with self.subTest(args=args):
                self.assertIsNone(retry.output_path(args, root))

    def test_jitter_grows_and_is_capped(self):
        class Ends:
            def uniform(self, low, high):
                return low, high
        self.assertEqual(retry.retry_delay(1, Ends()), (30, 60))
        self.assertEqual(retry.retry_delay(2, Ends()), (60, 120))
        self.assertEqual(retry.retry_delay(3, Ends()), (120, 240))
        self.assertEqual(retry.retry_delay(99, Ends()), (150, 300))

    def test_cancellation_stops_only_our_child(self):
        # A separate supervisor lets this test send SIGTERM only to its own PID.
        script = ('import codex_retry as r,sys; from pathlib import Path; '
                  'sys.exit(r.supervise(sys.argv[1:],Path(sys.argv[-2]),'
                  + repr(str(self.fake)) + ',delay=lambda n:0))')
        module_dir = str(Path(retry.__file__).resolve().parent)
        env = dict(os.environ, FAKE_LOG=str(self.log), FAKE_MODE='hang',
                   PYTHONPATH=module_dir + os.pathsep + os.environ.get('PYTHONPATH', ''))
        proc = subprocess.Popen([sys.executable, '-c', script, *self.args],
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, env=env)
        try:
            proc.stdin.write('original brief\n')
            proc.stdin.close()
            # Wait for the fake child to start (not the provider or another worker).
            until = time.monotonic() + 5
            while not self.log.exists() and time.monotonic() < until:
                time.sleep(.01)
            self.assertTrue(self.log.exists())
            proc.send_signal(signal.SIGTERM)
            self.assertEqual(proc.wait(timeout=8), 128 + signal.SIGTERM)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
            proc.stdout.close()


if __name__ == '__main__':
    unittest.main()
