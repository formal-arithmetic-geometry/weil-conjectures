#!/usr/bin/env python3
"""Run replay with a hard wall-clock deadline per BEGIN/END pair (exit 124 on timeout)."""
import argparse
import os
import queue
import signal
import subprocess
import sys
import threading
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--seconds', type=float, default=120)
parser.add_argument('--startup-seconds', type=float, default=120)
parser.add_argument('--total-seconds', type=float, default=600)
parser.add_argument('command', nargs=argparse.REMAINDER)
args = parser.parse_args()
command = args.command
if command and command[0] == '--':
    command = command[1:]
if not command:
    parser.error('missing replay command')
proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, bufsize=1, start_new_session=True)
lines = queue.Queue()

def read_lines():
    for line in proc.stdout:
        lines.put(line)
    lines.put(None)

threading.Thread(target=read_lines, daemon=True).start()
start = time.monotonic()
deadline = start + args.startup_seconds
current = 'startup'
try:
    while True:
        try:
            line = lines.get(timeout=max(0, min(deadline, start + args.total_seconds) - time.monotonic()))
        except queue.Empty:
            kind = 'total' if time.monotonic() >= start + args.total_seconds else 'declaration/startup'
            print(f'TIMEOUT {current}; limit={kind}; total={time.monotonic() - start:.3f}s',
                  flush=True)
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            sys.exit(124)
        if line is None:
            break
        print(line, end='', flush=True)
        if line.startswith('BEGIN '):
            current = line.strip()[6:]
            deadline = time.monotonic() + args.seconds
        elif line.startswith(('END ', 'COMPLETE ', 'LOADED ', 'REPLAY ')):
            current = 'between declarations'
            deadline = time.monotonic() + args.startup_seconds
    code = proc.wait()
    print(f'PROCESS exit={code} total={time.monotonic() - start:.3f}s', flush=True)
    sys.exit(code)
finally:
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
