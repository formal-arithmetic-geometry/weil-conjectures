#!/usr/bin/env python3
"""Stage-2 file compilation on the server against the live published build (tools/nt_srv_compile.py; side overlay retired 2026-10-19);
retried while the server is busy or unreachable; never compiled locally."""
import json
import os
import pathlib
import shlex
import subprocess
import sys

H = pathlib.Path.home()
PROJECT = os.environ.get("WEIL_PROJECT", "/home/ubuntu/weil-conjectures-sheaf")


def _die_with_parent():
    """2026-10-18 (waste): the ssh child gets SIGTERM when this process ends. Before, a worker that ended (or a
    scompile.py killed by its caller) left its ssh running as an orphan; the server call behind it compiled on for up
    to an hour for nobody (8 orphans of 54 calls at 19:30). With the ssh gone, the server call stops at once
    (tools/nt_srv_compile.py watches its pipes)."""
    import ctypes, signal
    try:
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGTERM)   # PR_SET_PDEATHSIG
    except (OSError, AttributeError):
        pass


def modname(f):
    parts = pathlib.Path(f).resolve().parts
    if "lean" not in parts:
        return "Sheaf.Stage2.Check"
    i = max(k for k, x in enumerate(parts) if x == "lean")
    return ".".join(parts[i + 1:])[:-5]


def server_overlay(files, texts=None):
    """2026-10-17: the same steps as the local overlay compile, run on the server against current sources, a failure
    confirmed there with tools/nt_compile.py as below. (rc, out), or None when the server tool is unavailable."""
    payload = {"files": {modname(f).replace(".", "/") + ".lean": (texts[str(f)] if texts else pathlib.Path(f).read_text()) for f in files}}
    cmd = ["ssh", "-i", str(H / "weil_formal.pem"), "-o", "ConnectTimeout=20",
           "-o", "ServerAliveInterval=15", "ubuntu@the project server",
           "cd " + shlex.quote(PROJECT) + " && nice -n 19 python3 tools/nt_srv_compile.py --wire-confirm"]
    try:
        # Progress lines arrive on stderr as the local compiler printed them.
        p = subprocess.run(cmd, input=json.dumps(payload), stdout=subprocess.PIPE, text=True,
                           timeout=60 * (2 * len(files) + 60) + 60, preexec_fn=_die_with_parent)
        value = json.loads(p.stdout.strip().splitlines()[-1])
        return int(value["rc"]), value["out"]
    except (subprocess.TimeoutExpired, ValueError, KeyError, IndexError, OSError):
        return None


sys.path.insert(0, str(H / "weil-launcher")); import compile_attach as CA
NO_ANSWER = "no answer from the server within"
def cacheable(result):
    return result[0] != 124   # a timeout is not stored (server load can cause it)
def server_dependency_stamp():
    """Include committed overlay sources and compiler tools, even while publication stays red."""
    command = ("cd " + shlex.quote(PROJECT) +
               " && git rev-parse HEAD:lean HEAD:tools"
               " && sha256sum local/builds/published local/builds/published.json local/builds/last.json")
    cmd = ["ssh", "-i", str(H / "weil_formal.pem"), "-o", "ConnectTimeout=20",
           "-o", "ServerAliveInterval=15", "ubuntu@the project server", command]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return p.stdout.strip() if p.returncode == 0 and p.stdout.strip() else None

def _runner_many(args, sources):
    """compile_attach runner: compile the caller's snapshot as run_many does."""
    return list(_direct_many(args["g"], args["item"], args["files"], {p: b.decode() for p, b in sources.items()}))
def run_many(g, item, files):
    """2026-10-25 (the human): one request in flight per task (these files), the result always reaches the caller, an
    identical request is answered from the stored result (compile_attach.py). The compile runs in a detached runner: a
    call that is cut off does not stop it, and the same command run again attaches to it."""
    if os.environ.get(CA.DIRECT):
        return _direct_many(g, item, files)
    files = [str(pathlib.Path(f).resolve()) for f in files]
    try:
        snap = {f: pathlib.Path(f).read_bytes() for f in files}
    except OSError as e:
        return 2, f"cannot read the source ({e}); nothing compiled"
    stamp = server_dependency_stamp()
    if stamp is None:
        return 2, "cannot read current server dependency state; no cached compile result reused; retry the compile"
    dep = CA.digest("server-source-state-v1", stamp)
    prio = os.path.basename(sys.argv[0]) == "deliver2.py"
    task = CA.digest(g, item, *files, prio)
    content = CA.digest(task, *[snap[f] for f in files], dep)
    spec = {"module": str(pathlib.Path(__file__).resolve()), "module_name": "scompile", "func": "_runner_many",
            "args": {"g": g, "item": item, "files": files}, "label": pathlib.Path(files[0]).name,
            "fail_result": [2, "compile tool fault: the compile runner stopped without a result (see ~/weil-launcher/compile-attach.log)"],
            "alive_paths": [str(pathlib.Path(files[0]).parent)]}
    r = CA.attach("s", task, content, dep, spec, snap, prio=prio)
    if isinstance(r, dict) and r.get("superseded"):
        return 3, ("NOT compiled: a newer version of these files was sent to compile while this request waited; this request "
                   "was withdrawn (one request per file at a time). Run the command again for the result of the current version.")
    return int(r[0]), r[1]
def _direct_many(g, item, files, texts=None):
    """2026-10-17: server only. A busy or unreachable server is retried with backoff for up to 60*(len+30)+30 s, then the
    call fails with exit code 124, as a server timeout did before; nothing is compiled on this machine."""
    print(f"Checking {len(files)} Lean file(s) on the server, one at a time.", file=sys.stderr, flush=True)
    import time
    t0 = time.time(); wait = 5   # 2026-10-25 (the human: never time out and rerun): retried until the server answers
    while True:
        r = server_overlay(files, texts)
        if r is not None:
            return r
        print(f"Server compile unavailable; retrying in {wait} s.", file=sys.stderr, flush=True)
        time.sleep(wait); wait = min(wait * 2, 30)


def run_server(g, item, files):
    payload = {"files": {modname(f).replace(".", "/") + ".lean":
                         pathlib.Path(f).read_text() for f in files}}
    cmd = ["ssh", "-i", str(H / "weil_formal.pem"), "-o", "ConnectTimeout=20",
           "-o", "ServerAliveInterval=15", "ubuntu@the project server",
           "cd " + shlex.quote(PROJECT) + " && nice -n 19 python3 tools/nt_compile.py --json"]
    try:
        p = subprocess.run(cmd, input=json.dumps(payload), capture_output=True, text=True,
                           timeout=60 * (len(files) + 30) + 30, preexec_fn=_die_with_parent)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as exc:
        def decoded(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        return 124, (decoded(exc.stdout) + decoded(exc.stderr) +
                     "\nServer connection timed out; each Lean invocation still has a 60 s limit.")


def run(g, item, f):
    return run_many(g, item, [f])


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--source":
        module = sys.argv[2]
        import re
        if not re.fullmatch(r"(?:Sheaf|WeilConjectures|Mathlib)(?:\.[A-Za-z_][A-Za-z0-9_']*)+", module):
            raise SystemExit("Expected a Lean module name")
        script = "import sys; sys.path.insert(0, 'tools'); import stage2_delivery as s; m=sys.argv[1]; p=(s.ROOT/'lean'/m.replace('.', '/')).with_suffix('.lean') if m.startswith('Sheaf.') else None; p=p if p and p.is_file() else s.existing_file(m); print(p.read_text() if p else 'Module source unavailable: '+m); sys.exit(0 if p else 1)"
        cmd = ["ssh", "-i", str(H / "weil_formal.pem"), "-o", "ConnectTimeout=20", "ubuntu@the project server", "cd " + shlex.quote(PROJECT) + " && python3 -c " + shlex.quote(script) + " " + shlex.quote(module)]
        raise SystemExit(subprocess.run(cmd).returncode)
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    rc, out = run_many(sys.argv[1], sys.argv[2], sys.argv[3:])
    print(out)
    raise SystemExit(rc)
