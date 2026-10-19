"""Replay the actual Q130 terminal failure through the deployed supervisor; no API calls."""
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('q130_retry', '/home/ubuntu/weil-launcher-all/codex_retry.py')
retry = importlib.util.module_from_spec(spec)
spec.loader.exec_module(retry)
evidence = json.loads((ROOT / 'EVIDENCE.json').read_text())
failed = evidence['failed_runs'][-1]
item = evidence['item']

with tempfile.TemporaryDirectory(prefix='q130-recovery-') as tmp:
    base = Path(tmp)
    last = base / 'run/Q130' / failed['attempt'] / 'last.txt'
    last.parent.mkdir(parents=True)
    fake = base / 'fake-codex'
    calls = base / 'calls.json'
    payload = base / 'failure.json'
    payload.write_text(json.dumps(failed))
    fake.write_text('''#!/usr/bin/env python3
import json, os, pathlib, sys
root = pathlib.Path(os.environ['Q130_REPLAY_ROOT'])
p = root / 'calls.json'
calls = json.loads(p.read_text()) if p.exists() else []
calls.append({'args': sys.argv[1:], 'prompt': sys.stdin.read()})
p.write_text(json.dumps(calls))
failure = json.loads((root / 'failure.json').read_text())
print('session id: ' + failure['session'], flush=True)
if len(calls) == 1 or os.environ.get('Q130_EXHAUST'):
    for line in failure['terminal_errors']: print(line, flush=True)
    sys.exit(1)
last = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])
last.write_text('READY ' + failure['attempt'].rsplit('.', 1)[0] + ': replay completed\\n')
''')
    fake.chmod(0o755)
    prompt = Path(failed['log_path']).with_name('prompt.txt').read_text()
    args = ['exec', '-c', 'model_providers.OpenAI.request_max_retries=30',
            '-c', 'model_providers.OpenAI.stream_max_retries=30',
            '-c', 'model_reasoning_effort=high', '-m', 'gpt-6.1-sol',
            '--dangerously-bypass-approvals-and-sandbox', '--skip-git-repo-check',
            '-C', '/home/ubuntu/weil-newtargets-shared', '-o', str(last), '-']
    assert retry.output_path(args, base / 'run') == last
    sleeps = []
    with patch.dict(os.environ, {'Q130_REPLAY_ROOT': str(base)}), patch('sys.stdin', io.StringIO(prompt)):
        rc = retry.supervise(args, last, fake, budget=2700,
            delay=lambda n: 31, sleep=sleeps.append, emit=lambda line: None)
    history = json.loads(calls.read_text())
    assert rc == 0 and last.read_text().startswith('READY ' + item)
    assert history[0]['prompt'] == prompt
    assert history[1]['args'][:2] == ['exec', 'resume']
    assert history[1]['args'][-2] == failed['session']
    assert sleeps == [30, 1]
    recovered_state = json.loads(last.with_name('codex-retry.json').read_text())
    assert recovered_state['status'] == 'answered'
    last.unlink()
    calls.unlink()
    with patch.dict(os.environ, {'Q130_REPLAY_ROOT': str(base), 'Q130_EXHAUST': '1'}), patch('sys.stdin', io.StringIO(prompt)):
        rc = retry.supervise(args, last, fake, budget=2700,
            max_recoveries=1, delay=lambda n: 0, sleep=lambda n: None, emit=lambda line: None)
    assert rc == 1 and last.read_text().startswith('BLOCKED ' + item)
    assert '6f23d5d1-7545-4c62-80f6-ee12c1050475' in last.read_text()
    assert 'READY' not in last.read_text()
    print('PASS: actual Q130 failure resumes its session; exhaustion retains the request ID and reports BLOCKED.')
