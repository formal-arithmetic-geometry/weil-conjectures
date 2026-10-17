#!/usr/bin/env python3
"""Recover dispatched workers from provider 429s without redoing their work.

Install at ~/weil-launcher-all/codex_retry.py and point ~/.local/bin/codex
at it. Only `exec ... -o ~/weil-launcher-all/run/.../last.txt` is supervised;
all other invocations exec the original, package-managed binary unchanged.
"""
import collections
from codex_admission import AdmissionTimeout, Gate
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import sys
import tempfile
import time


REAL = Path.home() / ".codex/packages/standalone/current/bin/codex"
RUN = Path.home() / "weil-launcher-all/run"
SESSION = re.compile(r"^session id: ([0-9a-f-]{36})\s*$")
RATE_LIMIT = re.compile(
    r"^ERROR: .*?(?:\b429\b|gateway_queue_full|Concurrency limit exceeded)", re.I)
PERMANENT = re.compile(r"insufficient_quota|billing|quota (?:exceeded|exhausted)", re.I)
MAX_RECOVERIES = 6


def resume_session(args):
    """Only an explicit session UUID can identify a dispatched resume safely."""
    if (len(args) >= 4 and args[:2] == ["exec", "resume"]
            and args[-1] == "-" and "--last" not in args
            and re.fullmatch(r"[0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}",
                             args[-2])):
        return args[-2]
    return None


def output_path(args, run_root=RUN):
    if not args or args[0] != "exec" or "--json" in args:
        return None
    # Deliberately cover only the dispatcher's exact noninteractive CLI shape.
    if len(args) < 2 or args[1] in ("review", "--help", "-h"):
        return None
    if args[1] == "resume" and resume_session(args) is None:
        return None
    result = None
    for i, arg in enumerate(args[:-1]):
        if arg in ("-o", "--output-last-message"):
            result = Path(args[i + 1])
    if result is None or not result.is_absolute() or result.name != "last.txt":
        return None
    try:
        relative = result.relative_to(run_root)
    except ValueError:
        return None
    if len(relative.parts) != 3 or ".." in relative.parts or args[-1] != "-":
        return None
    return result


def resume_args(args, session):
    # exec resume inherits the process cwd; unlike exec it has no -C option.
    # A dispatcher can itself resume a failed run. Replace its positional
    # session rather than nesting another `resume` and retaining the old UUID.
    resuming = resume_session(args) is not None
    options = []
    i = 2 if resuming else 1
    stop = len(args) - (2 if resuming else 1)
    while i < stop:
        if args[i] in ("-C", "--cd"):
            i += 2
        else:
            options.append(args[i])
            i += 1
    return ["exec", "resume", *options, session, "-"]


def worker_budget():
    """Leave time for the dispatcher to collect a diagnostic before its timeout."""
    try:
        parent = Path(f"/proc/{os.getppid()}/cmdline").read_bytes().split(b"\0")
        if Path(os.fsdecode(parent[0])).name == "timeout":
            return max(1.0, float(parent[1]) - 75)
    except (OSError, ValueError, IndexError):
        pass
    return 45 * 60 - 15


def retry_delay(failures, rng=random):
    maximum = min(300, 60 * 2 ** min(failures - 1, 3))
    return rng.uniform(maximum / 2, maximum)


class Stopped(Exception):
    def __init__(self, signum):
        self.signum = signum


def supervise(args, last, real=REAL, *, budget=None, max_recoveries=MAX_RECOVERIES,
              delay=retry_delay, sleep=time.sleep, emit=None):
    """Retry only failed CLI calls whose terminal diagnostic is a temporary 429."""
    if emit is None:
        def emit(line):
            sys.stdout.write(line)
            sys.stdout.flush()

    prompt = sys.stdin.read()
    deadline = time.monotonic() + (worker_budget() if budget is None else budget)
    state = {"status": "running", "recoveries": 0,
             "session_id": resume_session(args), "last_error": ""}
    child = None
    handlers = {}
    gate = Gate(real) if Path(real).resolve() == REAL.resolve() else None

    def record(status):
        state["status"] = status
        path = last.with_name("codex-retry.json")
        tmp = path.with_suffix(f".tmp-{os.getpid()}")
        tmp.write_text(json.dumps(state, indent=2) + "\n")
        tmp.replace(path)

    def diagnostic(status):
        record(status)
        if not last.exists() or not last.read_text().strip():
            item = last.parent.name.rsplit(".", 1)[0]
            message = (f"BLOCKED {item}: provider HTTP 429 persisted after "
                       f"{state['recoveries']} recovery attempts ({status}); "
                       f"sandbox retained. {state['last_error']}\n")
            tmp = last.with_suffix(f".tmp-{os.getpid()}")
            tmp.write_text(message)
            tmp.replace(last)

    def stop(signum, frame):
        raise Stopped(signum)

    for sig in (signal.SIGTERM, signal.SIGINT):
        handlers[sig] = signal.signal(sig, stop)
    try:
        current, text = args, prompt
        while True:
            record("running")
            if gate is not None:
                record("admission")
                gate.acquire(deadline, emit)
                record("running")
            # Keep the dispatcher's process group and timeout. No new session,
            # independent budget, or dispatcher state mutation is introduced.
            # A file avoids a pipe deadlock or BrokenPipeError when a large
            # brief or a startup/configuration failure precedes the first turn.
            with tempfile.TemporaryFile(mode="w+") as prompt_file:
                prompt_file.write(text)
                prompt_file.seek(0)
                child = subprocess.Popen([str(real), *current], stdin=prompt_file,
                                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                         text=True, errors="replace")
            errors = collections.deque(maxlen=3)
            missing_session = False
            for line in child.stdout:
                emit(line)
                match = SESSION.fullmatch(line.rstrip("\n"))
                if match:
                    state["session_id"] = match.group(1)
                if re.match(r"^Error: No saved session found with id\b", line):
                    missing_session = True
                if state["session_id"] and re.search(
                        r"failed to record rollout items: thread " +
                        re.escape(state["session_id"]) + r" not found", line):
                    # Q126: a printed session UUID can lack persisted history.
                    # Keep the sandbox and original brief as the recovery path.
                    state["session_id"] = None
                if line.startswith("ERROR:"):
                    errors.append(line.strip())
            child.stdout.close()
            rc = child.wait()
            if gate is not None:
                gate.release()
            # A real final answer always wins, even if an earlier turn hit 429.
            if last.exists() and last.read_text().strip():
                record("answered")
                return rc
            if missing_session and current[:2] == ["exec", "resume"]:
                # A missing saved thread cannot be resumed. Retry the original
                # role and brief within this same worker's existing deadline.
                state["session_id"] = None
                if time.monotonic() + 30 >= deadline:
                    diagnostic("worker budget")
                    return rc
                emit("[codex-retry] saved session unavailable; continuing with "
                     "the original brief and retained sandbox\n")
                current, text = args, prompt
                continue
            error = errors[-1] if errors else ""
            if rc == 0 or not RATE_LIMIT.search(error) or PERMANENT.search(error):
                record("exit")
                return rc
            state["last_error"] = error[:400]
            if gate is not None:
                gate.rate_limited()
            if state["recoveries"] >= max_recoveries:
                diagnostic("retry limit")
                return rc
            seconds = delay(state["recoveries"] + 1)
            if time.monotonic() + seconds + 30 >= deadline:
                diagnostic("worker budget")
                return rc
            state["recoveries"] += 1
            record("retrying")
            emit(f"[codex-retry] provider HTTP 429; recovery {state['recoveries']}/"
                 f"{max_recoveries} in {seconds:.1f}s; sandbox and session retained\n")
            # Short sleeps allow cancellation and progress during a long wait.
            remaining = seconds
            while remaining > 0:
                chunk = min(30, remaining)
                sleep(chunk)
                remaining -= chunk
            if state["session_id"]:
                current = resume_args(args, state["session_id"])
                text = ("Continue the same dispatched item from the interrupted turn. "
                        "The previous call ended with a provider HTTP 429. Keep the "
                        "original brief, sandbox and deadline; check any interrupted "
                        "tool's result before repeating a delivery or other mutation.\n")
            else:
                current, text = args, prompt
    except AdmissionTimeout as exc:
        record("admission timeout")
        item = last.parent.name.rsplit(".", 1)[0]
        if not last.exists() or not last.read_text().strip():
            tmp = last.with_suffix(f".tmp-{os.getpid()}")
            tmp.write_text(f"BLOCKED {item}: provider admission reached the worker budget "
                           f"({exc}); no API call was started; sandbox retained.\n")
            tmp.replace(last)
        return 75
    except Stopped as exc:
        # Only this supervisor's own child is signalled. The dispatcher's group
        # timeout also reaches that child and any tools it started.
        if child is not None and child.poll() is None:
            child.terminate()
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        if state["last_error"]:
            diagnostic("worker stopped")
        return 128 + exc.signum
    finally:
        if gate is not None:
            gate.release()
        for sig, handler in handlers.items():
            signal.signal(sig, handler)


def main():
    args = sys.argv[1:]
    last = output_path(args)
    if last is None:
        os.execv(str(REAL), [str(REAL), *args])
    return supervise(args, last)


if __name__ == "__main__":
    sys.exit(main())
