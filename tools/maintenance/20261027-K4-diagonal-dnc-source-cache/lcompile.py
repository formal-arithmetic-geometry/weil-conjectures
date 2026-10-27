#!/usr/bin/env python3
"""Compile Lean files of this project ON THE PROJECT SERVER (~/cc1/rset.py) against its live published build. Since
2026-10-17 nothing is compiled on this machine; a busy or unreachable server is retried until it answers (2026-10-25: never a give-up).

    lcompile.py <file.lean>                    one file
    lcompile.py <a.lean> <b.lean> [...]        several files of one sandbox that import one another (a new module and the
                                               module that imports it): compiled in import order, each written as a compiled
                                               module to <sandbox>/.lbuild, where the later ones find it
    lcompile.py --all <sandbox directory>      every .lean file under <sandbox>/lean, the same way

A file that lies under a directory named lean/ (…/lean/Sheaf/Foo/Bar.lean) is compiled as the module Sheaf.Foo.Bar. A single
file also sees the modules already compiled into its sandbox's .lbuild (the output says so; compile the set again after
changing one of them). The .lbuild directory contains only sandbox outputs; Lean --setup resolves those modules
explicitly, and LEAN_PATH resolves the shared library and packages without a link farm. Every file is a file of Lean's module system (`module`, `public import`, `@[expose] public section`).

Prints the compiler's messages: errors, warnings, and the goals at an unfinished proof ("unsolved goals"; a `sorry` left
shows as "declaration uses sorry" only with -Dwarn.sorry=true, which this command does not set: grep your file). A compile waits
in a shared queue, often minutes; the command waits for the result and never gives up; a command cut off is run again
unchanged and re-attaches to the same job. The server compile (scompile.py, and the one inside deliver3.py) stays the final check: a module landed in the last two
minutes may not be here yet. The options are those of lean/lakefile.toml; `autoImplicit = false` is added for every file that
is not of the source library (a path with /WeilConjectures/ or /Comparator/, or a file name starting with WeilConjectures_),
as the server's tools/lean_file.sh does."""
import json, os, pathlib, re, subprocess, sys, tempfile, time
H = pathlib.Path.home(); P = H / "weil-lean"; BUILD = P / ".lake/build/lib/lean"
ENV = dict(os.environ, PATH=str(H / ".elan" / "bin") + ":" + os.environ.get("PATH", ""))
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$", re.M)
def base_opts():
    out = []; on = False
    for l in (P / "lakefile.toml").read_text().split("\n"):
        if l.startswith("[leanOptions]"): on = True; continue
        if l.startswith("["): on = False
        m = re.match(r"([A-Za-z][\w.]*)\s*=\s*([^#]*)", l) if on else None
        if m: out.append(f"-D{m.group(1)}={m.group(2).strip().strip(chr(34))}")
    return out
def upstream(f):
    s = str(pathlib.Path(f).resolve())
    return "/WeilConjectures/" in s or "/Comparator/" in s or pathlib.Path(f).name.startswith("WeilConjectures_")
def lean_root(f):
    """The directory named lean/ above the file (the root its module name is read from), or None."""
    parts = pathlib.Path(f).resolve().parts
    ks = [k for k, x in enumerate(parts[:-1]) if x == "lean"]
    return pathlib.Path(*parts[:ks[-1] + 1]) if ks else None
def modname(f):
    r = lean_root(f)
    return ".".join(pathlib.Path(f).resolve().relative_to(r).with_suffix("").parts) if r else pathlib.Path(f).stem
def lean_path(first=None):
    ps = ([str(first)] if first else []) + [str(BUILD)] + sorted(str(x) for x in (P / ".lake/packages").glob("*/.lake/build/lib/lean"))
    return ":".join(ps)
def output_parent(lb, rel):
    """Make only the output's ancestors real; never write through old farm links."""
    dst = pathlib.Path(lb)
    for part in rel.parts[:-1]:
        dst = dst / part
        if dst.is_symlink(): dst.unlink()
        dst.mkdir(exist_ok=True)

def local_artifacts(lb):
    """Index only real sandbox modules, without following any library symlinks.

    Lean 4.33 selects whole package roots in LEAN_PATH. --setup overrides just
    these local modules (including transitive imports), leaving shared imports
    on the normal search path. Keep every available module/IR companion.
    """
    arts = {}
    def visit(directory):
        with os.scandir(directory) as entries:
            for entry in entries:
                if entry.is_symlink(): continue
                if entry.is_dir(follow_symlinks=False):
                    visit(pathlib.Path(entry.path))
                elif entry.name.endswith(".olean"):
                    p = pathlib.Path(entry.path)
                    name = ".".join(p.relative_to(lb).with_suffix("").parts)
                    oleans = [str(p)]
                    for suffix in (".olean.server", ".olean.private"):
                        q = p.with_suffix(suffix)
                        if not q.is_file(): break
                        oleans.append(str(q))
                    ir = []
                    for suffix in (".ir.sig", ".ir"):
                        q = p.with_suffix(suffix)
                        if not q.is_file(): break
                        ir.append(str(q))
                    arts[name] = [oleans, ir]
    if lb: visit(pathlib.Path(lb))
    # 2026-10-22 (the human; a root fix passed its sandbox compile and failed the global build on a stale sibling): an
    # artifact of a module whose sandbox source is byte-identical to the library's (shared clone, origin HEAD) or has no
    # sandbox source is stale or redundant; the published build serves it. Only modules the sandbox changed or created
    # keep their artifacts, and those are the modules a delivery carries.
    try:
        if lb:
            sb_lean = pathlib.Path(lb).parent / "lean"
            lib_lean = pathlib.Path.home() / "weil-conjectures-sheaf-shared" / "lean"
            for name in list(arts):
                rel = pathlib.Path(*name.split(".")).with_suffix(".lean")
                src = sb_lean / rel; lib = lib_lean / rel
                if not src.is_file() or (lib.is_file() and src.read_bytes() == lib.read_bytes()):
                    del arts[name]
    except OSError:
        pass
    return arts

_ORIG_LOCAL_ARTIFACTS = local_artifacts   # the side project's tools replace local_artifacts (their overlay): they stay local

import contextlib, fcntl, shlex
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent)); import compile_attach as CA
SLOTS = int(os.environ.get("LCOMPILE_SLOTS", "32"))   # 2026-10-22: local compiles again (lset.py); 16 at once: memory (deliveries hold 1-3 GB each too)
LSET = pathlib.Path.home() / "weil-launcher" / "lset.py"
# 2026-10-26 (the human): the compile service (tools/remote_compile_set.py, here through lset.py, on the server through
# the spool) lets Lean run up to RUN_LIMIT s so the slow declaration finishes and reports; a run over `timeout` (60 s) is
# still NOT accepted (exit 124). The waits below cover RUN_LIMIT per file plus the service's own slot wait.
RUN_LIMIT = int(os.environ.get("SHEAF_FILE_RUN_LIMIT", "300"))
MIRROR_STAMP = pathlib.Path.home() / "weil-conjectures-sheaf-shared" / "local" / "builds" / "published"
def _local_ok():
    """2026-10-22 (the human): a share of the compiles runs here against the mirrored published build (pubmirror.sh),
    when lset.py exists, LCOMPILE_NO_LOCAL is unset and the mirror stamp is younger than 30 min (the mirror loop is alive)"""
    try:
        # 2026-10-23: liveness is the mirror loop's own log (written every rsync, ~60 s), not the published stamp, which
        # only moves on a green build: 3 h without one (an upstream sync) sent every compile to the server (queue 1300)
        beat = pathlib.Path.home() / "weil-launcher-all" / "pubmirror.log"
        return LSET.is_file() and not os.environ.get("LCOMPILE_NO_LOCAL") and time.time() - beat.stat().st_mtime < 600
    except OSError:
        return False
# 2026-10-25 (the human): no idle wait for a local slot. LOCAL_WAIT (300 s, 2026-10-23) made a call queue here for a
# local slot before it went to the server, because the server queue then took 5-20 min and a local slot usually freed
# sooner; it left calls idle for up to 5 min while server slots were free. Now: a free local slot now, else the spool.
SERVER = "ubuntu@the project server"; SSH_KEY = str(pathlib.Path.home() / "weil_formal.pem")
_SNAP = {}
def take_slot():
    """A free local compile slot (a locked file), or None. At most SLOTS compiles at once on this machine."""
    d = pathlib.Path.home() / "weil-launcher" / ".lslots"; d.mkdir(exist_ok=True)
    n = SLOTS
    try:   # 2026-10-24 (the human): the cap follows the load, written by ~/weil-launcher/slot-governor.py
        n = int((pathlib.Path.home() / "weil-launcher" / "local-slots.cap").read_text())
    except (OSError, ValueError):
        pass
    for i in range(n):
        f = open(d / f"{i}", "w")
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); return f
        except OSError:
            f.close()
    return None
def remote(rel, text, timeout):
    """Compile on the project server against its published build (~/cc1/rcompile.py; the human, 2026-10-13: when the
    local slots are full). One multiplexed ssh connection is shared by all workers (no connection storm). Returns
    (exit code, output), or None when the server is busy or unreachable."""
    # sshd allows 10 sessions per connection (MaxSessions): spread over MUX connections
    cp = str(pathlib.Path.home() / ".ssh" / f"cm-weil-rcompile-{os.getpid() % int(os.environ.get('LCOMPILE_MUX', '3'))}")
    cmd = ["ssh", "-i", SSH_KEY, "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=20", "-o", "ControlMaster=auto",
           "-o", f"ControlPath={cp}", "-o", "ControlPersist=600", "-o", "ServerAliveInterval=30", SERVER,
           f"python3 ~/cc1/rcompile.py {shlex.quote(str(rel))} {int(timeout)}"]
    try:
        p = subprocess.run(cmd, input=text, capture_output=True, text=True, timeout=timeout + 90)
    except subprocess.TimeoutExpired:
        return None
    if p.returncode in (75, 255) or "rcompile" not in p.stdout + p.stderr and p.returncode != 0 and not p.stdout:
        return None
    return p.returncode, p.stdout + p.stderr

RSET_MUX = int(os.environ.get("LCOMPILE_MUX", "8"))
DOWN = pathlib.Path.home() / "weil-launcher" / ".rset-down"
RLOG = pathlib.Path.home() / "weil-launcher" / "lcompile-remote.log"
def _log(kind, n, secs):
    try:
        with open(RLOG, "a") as fh: fh.write(f"{time.strftime('%F %T')} {kind} files={n} {secs:.1f}s pid={os.getpid()}\n")
    except OSError: pass
def remote_jobs(jobs, root, lb, timeout, stop_on_fail=False):
    """Compile on the project server (~/cc1/rset.py; 2026-10-17: every compile runs there, none on this machine): one call
    carries the sources of all `jobs` [(file, out, probe)] and the sandbox's compiled modules (.lbuild); the server compiles
    them in the given order against the live published build and returns, per job, (exit code, output with this machine's
    paths) and writes the compiled modules of the `out` jobs into `lb`. A busy or unreachable server is retried with backoff
    until it answers (2026-10-25: no give-up budget)."""
    if local_artifacts is not _ORIG_LOCAL_ARTIFACTS:
        return [(2, "this compile used a replaced local_artifacts (a side overlay); side-project files compile on the server "
                    "with ~/weil-launcher-nt/scompile.py")] * len(jobs)
    # 2026-10-24 (the human: workers deleted their probe files while a call waited, and the call then failed on every
    # retry): the sources are read once, here, and every attempt compiles this snapshot
    for f, _o, _p in jobs:
        if os.environ.get(CA.DIRECT) and str(f) in _SNAP: continue   # a runner: the caller's snapshot
        try:
            _SNAP[str(f)] = pathlib.Path(f).read_bytes()
        except OSError as e:
            return [(2, f"{f}: cannot read the source ({e.strerror}); nothing compiled")] * len(jobs)
    if not os.environ.get(CA.DIRECT):
        return _attached(jobs, root, lb, timeout, stop_on_fail)
    # 2026-10-25 (the human: never time out and rerun): no give-up budget. A submitted job keeps its place in the spool and
    # this call waits for its result; only a tool fault that repeats unchanged is answered (as a tool fault, rc 2).
    t0 = time.time(); wait = 5; same_fault = [None, 0]
    if lb is not None and not pathlib.Path(lb).is_dir():
        if pathlib.Path(lb).parent.is_dir(): pathlib.Path(lb).mkdir(exist_ok=True)   # the worker removed .lbuild meanwhile
        else: return [(2, f"the sandbox {pathlib.Path(lb).parent} no longer exists; nothing compiled")] * len(jobs)
    if _local_ok():   # 2026-10-22: first a local slot; a busy or failing local service sends the call to the server
        slot = take_slot()   # 2026-10-25: no wait; a busy local service sends the call to the spool at once
        if slot is not None:
            try:
                r = _remote_jobs(jobs, root, lb, timeout, stop_on_fail, local=True)
            except Exception as e:
                _log(f"local-error-{type(e).__name__}", len(jobs), time.time() - t0); r = None
            finally:
                slot.close()
            if r is not None: return r
    while True:
        try:
            r = _remote_jobs(jobs, root, lb, timeout, stop_on_fail)
        except Exception as e:
            _log(f"remote-error-{type(e).__name__}", len(jobs), time.time() - t0); r = None
            try:
                with open(RLOG, "a") as fh: fh.write(f"    detail: {str(e)[:200]}\n")   # 2026-10-24: which file went missing
            except OSError: pass
            fault = f"{type(e).__name__}: {str(e)[:300]}"
            same_fault = [fault, same_fault[1] + 1] if same_fault[0] == fault else [fault, 1]
            if same_fault[1] >= 5:   # the same exception five times in a row: a tool fault, reported with its text
                return [(2, f"compile tool fault (not a Lean result; the launcher maintainer is told by this log): {fault}")] * len(jobs)
        if r is not None: return r
        time.sleep(wait); wait = min(wait * 2, 30)
SPOOL = "weil-conjectures-sheaf/local/compile-spool"
SPOOL_POLL = float(os.environ.get("LCOMPILE_SPOOL_POLL", "60"))
LOCAL_STEAL_EVERY = float(os.environ.get("LCOMPILE_LOCAL_STEAL_EVERY", "5"))   # s between tries for a freed local slot
def _spool(data, cp):
    """2026-10-23 (the human): no ssh call waits for a compile any more. The job goes into the server's spool
    (~/cc1/compile-spool.py feeds it to rset.py); this process looks for its result once a minute, collects it and
    deletes it. Returns an object with .returncode/.stdout, or None when the upload failed (the caller retries)."""
    import types
    # 2026-10-25 (spool-prio): the spool serves its queue in name order. A delivery (deliver3.py) holds one of the few
    # delivery slots while its compile waits, and its worker has nothing left to do but wait; at 22:00-02:00 on 10-24/25
    # it queued behind up to 3900 exploratory compiles for 1-3.7 h. A delivery's job name starts with "0", which sorts
    # before every ordinary name (time_ns, "17..."), so it is served next; it still needs an ordinary server slot.
    prio = os.path.basename(sys.argv[0]) == "deliver3.py" or bool(os.environ.get("LCOMPILE_PRIO"))   # (runner: set by compile_attach)
    jid = ("0" if prio else "") + f"{time.time_ns()}-codex-{os.getpid()}"
    ssh = ["ssh", "-i", SSH_KEY, "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=20", "-o", "ControlMaster=auto",
           "-o", f"ControlPath={cp}", "-o", "ControlPersist=600", "-o", "ServerAliveInterval=30", SERVER]
    # 2026-10-25 (attach): a runner records its spool job id; a runner started after it died adopts that job (still
    # queued, running, or finished and uncollected) instead of uploading it again at the back of the queue
    ck = os.environ.get("COMPILE_ATTACH_CK"); jidf = CA.RES / f"{ck}.jid" if ck else None
    adopted = False
    try:
        old = jidf.read_text().strip() if jidf and time.time() - jidf.stat().st_mtime < 12 * 3600 else ""
    except OSError:
        old = ""
    if old:
        try:
            r = subprocess.run(ssh + [f"touch -c {SPOOL}/in/{old}.hb; test -e {SPOOL}/in/{old}.tar -o -e {SPOOL}/out/{old}.rc && echo yes"],
                               capture_output=True, timeout=60)
            if r.stdout.decode().strip() == "yes": jid = old; adopted = True; _log("spool-adopted", 0, 0)
        except subprocess.TimeoutExpired:
            pass
    _CUR.update(jid=jid, ssh=ssh)
    try:
        if adopted: raise StopIteration
        # 2026-10-25 (heartbeat): in/<id>.hb is touched at every poll; the spool answers a job whose caller stopped
        # polling (killed by a tool timeout or a session restart) with exit 75 instead of compiling it for nobody
        up = subprocess.run(ssh + [f"cat > {SPOOL}/in/{jid}.tar.part && touch {SPOOL}/in/{jid}.hb && "
                                   f"mv {SPOOL}/in/{jid}.tar.part {SPOOL}/in/{jid}.tar"],
                            input=data, capture_output=True, timeout=180)
        if up.returncode: return None
        if jidf: jidf.write_text(jid)
    except StopIteration:
        pass
    except subprocess.TimeoutExpired:
        return None
    steal = True
    while True:   # 2026-10-25: no deadline; the spool answers every job it holds
        # 2026-10-25 (fairq): the job waits in the spool, and meanwhile a local slot that frees takes it (no idle wait:
        # the job is queued from the start). With the 300-s local wait gone, freed local slots stood idle while the
        # spool queue grew (local results/min 50 -> 39, median round trip 61 s -> 303 s, 14:12-14:42).
        t_poll = time.time() + SPOOL_POLL
        while time.time() < t_poll:
            time.sleep(LOCAL_STEAL_EVERY)
            if not steal or not _local_ok(): continue
            slot = take_slot()
            if slot is None: continue
            try:
                w = subprocess.run(ssh + [f"if [ -e {SPOOL}/out/{jid}.tar.part ] || [ -e {SPOOL}/out/{jid}.rc ]; then echo started; "
                                          f"else rm -f {SPOOL}/in/{jid}.tar {SPOOL}/in/{jid}.hb && echo withdrawn; fi"],
                                   capture_output=True, timeout=60).stdout.decode().strip()
            except subprocess.TimeoutExpired:
                w = ""
            if w == "withdrawn":
                if jidf: jidf.unlink(missing_ok=True)
                _CUR.clear(); return types.SimpleNamespace(slot=slot)
            slot.close()
            if w == "started": steal = False
        try:
            r = subprocess.run(ssh + [f"touch -c {SPOOL}/in/{jid}.hb; cat {SPOOL}/out/{jid}.rc 2>/dev/null || "
                                      f"[ -e {SPOOL}/in/{jid}.tar ] || [ -e {SPOOL}/out/{jid}.tar.part ] || echo LOST"],
                               capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            continue
        rc = r.stdout.decode().strip()
        if rc == "LOST":   # 2026-10-25: neither queued, running nor answered (collected by a twin runner): submit again
            if jidf: jidf.unlink(missing_ok=True)
            _CUR.clear(); return None
        if not rc.lstrip("-").isdigit(): continue
        try:
            g = subprocess.run(ssh + [f"cat {SPOOL}/out/{jid}.tar && rm -f {SPOOL}/out/{jid}.tar {SPOOL}/out/{jid}.rc "
                                      f"{SPOOL}/in/{jid}.hb"],
                               capture_output=True, timeout=300)
        except subprocess.TimeoutExpired:
            continue
        if g.returncode: continue
        if jidf: jidf.unlink(missing_ok=True)
        _CUR.clear()
        return types.SimpleNamespace(returncode=int(rc), stdout=g.stdout, stderr=b"")
_CUR = {}
def cancel():
    """compile_attach: this runner's request was replaced by a newer one of the same task (or has no caller left):
    withdraw a queued spool job; a job already running is discarded by the spool when it ends (its in/ file is gone)."""
    if _CUR.get("jid"):
        j = _CUR["jid"]
        subprocess.run(_CUR["ssh"] + [f"rm -f {SPOOL}/in/{j}.tar {SPOOL}/in/{j}.hb {SPOOL}/out/{j}.tar {SPOOL}/out/{j}.rc"],
                       capture_output=True, timeout=60)
        ck = os.environ.get("COMPILE_ATTACH_CK")
        if ck: (CA.RES / f"{ck}.jid").unlink(missing_ok=True)
def _own_modules(jobs, root):
    return {".".join(f.relative_to(root).with_suffix("").parts) for f, _o, _p in jobs}
def _source_tree():
    """Committed sources also supply unpublished dependencies in the private overlay."""
    try:
        p = subprocess.run(["git", "rev-parse", "HEAD:lean"], cwd=H / "weil-conjectures-sheaf-shared",
                           capture_output=True, text=True, timeout=10)
        if p.returncode == 0 and p.stdout.strip(): return p.stdout.strip()
    except (OSError, subprocess.TimeoutExpired):
        pass
    # If the snapshot cannot be read, compile normally but do not reuse a result
    # whose unpublished dependencies might have changed.
    return f"unavailable:{time.time_ns()}"
def _dep(jobs, root, lb):
    """Publication, committed Lean sources and the sandbox artifacts other than this call's.

    The compile service supplies missing published objects from committed sources.
    A source repair must invalidate old diagnostics even before a new green build.
    Use the Lean tree, so metadata-only commits keep cached results reusable.
    """
    sig = []
    try:
        own = _own_modules(jobs, root)
        for name, (oleans, ir) in sorted(local_artifacts(lb).items()):
            if name in own: continue
            for x in oleans:
                st = os.stat(x); sig.append(f"{name}:{st.st_size}:{st.st_mtime_ns}")
    except OSError:
        sig.append("?")
    return CA.digest(CA.published_stamp(), _source_tree(), *sig)
NO_ANSWER = "no answer from the compile server"
def cacheable(result):
    # a timeout is not stored (server load can cause it); it still reaches every caller attached to the request
    # 2026-10-26: nor a missing dependency object file (the mirror was being rewritten by a stray `lake build`)
    return not any(rc == 124 or "cannot read the source" in (t or "") or "replaced local_artifacts" in (t or "")
                   or ("object file" in (t or "") and "does not exist" in (t or ""))
                   for rc, t in result)
def _runner_jobs(args, sources):
    """compile_attach runner: compile the caller's snapshot (sources) as remote_jobs does."""
    _SNAP.update({p: b for p, b in sources.items()})
    os.environ["COMPILE_ATTACH_CK"] = os.environ.get("COMPILE_ATTACH_CK") or args["ck"]
    jobs = [(pathlib.Path(f), o, p) for f, o, p in args["jobs"]]
    return [list(x) for x in remote_jobs(jobs, pathlib.Path(args["root"]), pathlib.Path(args["lb"]) if args["lb"] else None,
                                         args["timeout"], args["stop_on_fail"])]
def _attached(jobs, root, lb, timeout, stop_on_fail):
    """2026-10-25 (the human): one request in flight per task, every result reaches the worker (compile_attach.py)."""
    prio = os.path.basename(sys.argv[0]) == "deliver3.py"
    paths = sorted((str(f), bool(o), bool(p)) for f, o, p in jobs)
    task = CA.digest(json.dumps(paths), stop_on_fail, prio)
    content = CA.digest(task, timeout, *[x for f, o, p in jobs for x in (str(f), str(o), p, _SNAP[str(f)])])
    dep = _dep(jobs, root, lb)
    n = len(jobs)
    def valid(result):
        for (f, o, p), (rc, _t) in zip(jobs, result):
            if o and not p and rc == 0 and not (pathlib.Path(o) / f.relative_to(root).with_suffix(".olean")).is_file(): return False
        return True
    spec = {"module": str(pathlib.Path(__file__).resolve()), "module_name": "lcompile", "func": "_runner_jobs",
            "args": {"jobs": [[str(f), str(o) if o else None, p] for f, o, p in jobs], "root": str(root),
                     "lb": str(lb) if lb else None, "timeout": timeout, "stop_on_fail": stop_on_fail, "ck": "l" + content},
            "label": pathlib.Path(str(jobs[0][0])).name + (f"+{n - 1}" if n > 1 else ""),
            "fail_result": [[2, "compile tool fault: the compile runner stopped without a result (see ~/weil-launcher/compile-attach.log)"]] * n,
            "alive_paths": [str(root.parent)]}
    r = CA.attach("l", task, content, dep, spec, {str(f): _SNAP[str(f)] for f, _o, _p in jobs}, valid=valid, prio=prio)
    if isinstance(r, dict) and r.get("superseded"):
        return [(3, "NOT compiled: a newer version of these files was sent to compile while this request waited; this request "
                    "was withdrawn (one request per file at a time). Run the command again for the result of the current version.")] * n
    return [tuple(x) for x in r]
def _remote_jobs(jobs, root, lb, timeout, stop_on_fail, local=False):
    import io, tarfile
    t0 = time.time(); buf = io.BytesIO(); man = {"timeout": int(timeout), "stop_on_fail": stop_on_fail, "jobs": []}
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=3) as t:
        for f, out, probe in jobs:
            rel = f.relative_to(root)
            src = _SNAP.get(str(f))
            if src is None: t.add(str(f), arcname="lean/" + str(rel))
            else:
                ti = tarfile.TarInfo("lean/" + str(rel)); ti.size = len(src); ti.mtime = int(time.time()); t.addfile(ti, io.BytesIO(src))
            man["jobs"].append({"rel": str(rel), "upstream": upstream(f), "out": bool(out), "probe": probe or ""})
        for name, (oleans, ir) in local_artifacts(lb).items():
            for x in oleans + ir: t.add(x, arcname=".lbuild/" + str(pathlib.Path(x).relative_to(lb)))
        m = json.dumps(man).encode(); ti = tarfile.TarInfo("manifest.json"); ti.size = len(m); t.addfile(ti, io.BytesIO(m))
    kind = "local" if local else "remote"
    if local:
        cmd = [sys.executable, str(LSET)]; env = dict(os.environ, SHEAF_COMPILE_SLOTS=str(SLOTS))
    else:
        cp = str(pathlib.Path.home() / ".ssh" / f"cm-weil-rset-{os.getpid() % RSET_MUX}")
        cmd = ["ssh", "-i", SSH_KEY, "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=20", "-o", "ControlMaster=auto",
               "-o", f"ControlPath={cp}", "-o", "ControlPersist=600", "-o", "ServerAliveInterval=30", SERVER, "python3 ~/cc1/rset.py"]; env = None
    if local:
        try:
            p = subprocess.run(cmd, input=buf.getvalue(), capture_output=True, timeout=(max(timeout, RUN_LIMIT) + 60) * len(jobs) + 600, env=env)
        except subprocess.TimeoutExpired:
            _log(f"{kind}-timeout", len(jobs), time.time() - t0); return None
    else:
        p = _spool(buf.getvalue(), cp)
        if p is None:
            _log("spool-upload-failed", len(jobs), time.time() - t0); return None
        if getattr(p, "slot", None) is not None:   # a local slot freed while the job waited in the spool: compile here
            slot = p.slot; local = True; kind = "local-from-spool"
            try:
                p = subprocess.run([sys.executable, str(LSET)], input=buf.getvalue(), capture_output=True,
                                   timeout=(max(timeout, RUN_LIMIT) + 60) * len(jobs) + 600, env=dict(os.environ, SHEAF_COMPILE_SLOTS=str(SLOTS)))
            except subprocess.TimeoutExpired:
                _log(f"{kind}-timeout", len(jobs), time.time() - t0); return None
            finally:
                slot.close()
    if p.returncode != 0 or not p.stdout:
        _log(f"{kind}-busy" if p.returncode == 75 else f"{kind}-fail-{p.returncode}", len(jobs), time.time() - t0); return None
    try:
        t = tarfile.open(fileobj=io.BytesIO(p.stdout), mode="r:gz")
        res = json.loads(t.extractfile("result.json").read()); members = {x.name: x for x in t.getmembers() if x.isfile()}
    except Exception:
        _log(f"{kind}-badreply", len(jobs), time.time() - t0); return None
    td = res["td"]; outs = []
    byrel = {str(f.relative_to(root)): (f, out, probe) for f, out, probe in jobs}
    for r in res["results"]:
        f, out, probe = byrel[r["rel"]]
        if out and not probe:
            rel = f.relative_to(root); o = pathlib.Path(lb) / rel.with_suffix(".olean"); output_parent(pathlib.Path(lb), rel)
            for x in o.parent.glob(o.stem + ".*"): x.unlink()
            pre = ".lbuild/" + str(rel.with_suffix(""))
            for name, mem in members.items():
                if name.startswith(pre + ".") and "/" not in name[len(pre):]:
                    (pathlib.Path(lb) / name[len(".lbuild/"):]).write_bytes(t.extractfile(mem).read())
        if r["rc"] == 124 and r["out"] is None:
            outs.append((124, f"NOT ACCEPTED: stopped after {max(timeout, RUN_LIMIT)} s, the longest a compile may run (the limit for one file is {timeout} s): the fault is usually a definition that is expensive to unfold, not the limit")); continue
        text = r["out"].replace(td + "/lean", str(root)).replace(td + "/.lbuild", str(lb or root.parent / ".lbuild")).replace(td, str(root.parent))
        note = f"(with the modules compiled into {lb}) " if lb and not out and r["arts"] else ""
        outs.append((r["rc"], text + f"\n{note}[{r['secs']:.1f} s]"))
    if local and any(("failed to open file" in (o or "") and ".olean" in (o or ""))
                     or re.search(r"error: object file [^\n]+ does not exist", o or "")
                     or "lset.py" in (o or "") for _, o in outs):
        # The mirror omits Lake traces, so a missing transitive object may need
        # the server's dependency resolver. A local service failure also retries there.
        _log("local-missing", len(jobs), time.time() - t0); return None
    _log(kind, len(jobs), time.time() - t0)
    return outs

NOTICE = pathlib.Path.home() / "weil-launcher" / "compile-notice.txt"
def notice():
    """The launcher's notice about a compile-service fault (shown for 24 h after it is written), else empty."""
    try:
        if time.time() - NOTICE.stat().st_mtime < 86400: return NOTICE.read_text().strip() + "\n\n"
    except OSError: pass
    return ""
def run(f, timeout=60, out=None, probe="", try_remote=True):
    """Compile one file on the project server (remote_jobs). `out`: the directory compiled modules of the sandbox are
    written to and read from (the file is written there too, as a module others can import). `probe`: text appended to a
    temporary copy (deliver3.py). A file outside any lean/ directory compiles as the module named by its file name.
    `try_remote` is kept for old callers and ignored: there is no local compile (2026-10-17)."""
    f = pathlib.Path(f).resolve(); root = lean_root(f)
    if root is None:
        root = f.parent; out = None; lb = None
    else:
        lb = pathlib.Path(out) if out else ((root.parent / ".lbuild") if (root.parent / ".lbuild").is_dir() else None)
    return remote_jobs([(f, out, probe)], root, lb, timeout)[0]
def order(files):
    """The files, a module after the siblings it imports."""
    mods = {modname(f): pathlib.Path(f) for f in files}
    imp = {m: [d for d in IMPORT.findall(p.read_text()) if d in mods and d != m] for m, p in mods.items()}
    out = []; left = dict(imp)
    while left:
        ready = sorted(m for m, ds in left.items() if not [d for d in ds if d in left])
        if not ready: raise SystemExit("the modules import one another in a cycle: " + ", ".join(left))
        for m in ready: out.append(mods[m]); del left[m]
    return out
def run_set(files, timeout=60):
    """Compile several files of one sandbox in import order; returns (exit code, output, [(file, exit code)])."""
    files = [pathlib.Path(f).resolve() for f in files]; roots = {lean_root(f) for f in files}
    if len(roots) != 1 or None in roots: return 2, "the files must lie under one directory named lean/ (the sandbox mirrors the repository)", []
    lb = roots.pop().parent / ".lbuild"; lb.mkdir(exist_ok=True)
    rc = 0; text = []; per = []; fs = order(files)
    rr = remote_jobs([(f, lb, "") for f in fs], lean_root(fs[0]), lb, timeout, stop_on_fail=True)
    for k, f in enumerate(fs):
        if k >= len(rr): break
        r, o = rr[k]
        per.append((f, r)); rc = rc or r
        text.append(f"== {modname(f)} ({'compiled' if r == 0 else 'NOT compiled'})\n{o.strip()}")
        if r: text.append("(stopped here: the modules after this one may import it)"); break
    return rc, "\n".join(text), per
if __name__ == "__main__":
    fs = sys.argv[1:]
    if not fs or fs[0] in ("-h", "--help", "help"): raise SystemExit(__doc__)
    # 2026-10-24: a name that is not a file used to queue for a compile slot and fail 6 minutes later
    # (72 calls of `lcompile.py --help` in 10 min); answer at once
    _missing = [f for f in fs if f != "--all" and not f.startswith("-") and not pathlib.Path(f).exists()] if fs[0] != "--all" else []
    if _missing: raise SystemExit("no such file: " + ", ".join(_missing) + "\n\n" + (__doc__ or ""))
    _flags = [f for f in fs if f.startswith("-") and f != "--all"]
    if _flags: raise SystemExit("unknown option(s): " + " ".join(_flags) + "\n\n" + (__doc__ or ""))
    if fs[0] == "--all":
        fs = sorted(str(x) for x in (pathlib.Path(fs[1]) / "lean").rglob("*.lean") if not x.name.endswith("__probe.lean"))
        if not fs: raise SystemExit("no .lean file under " + sys.argv[2] + "/lean")
    # 2026-10-24 (the human: the result of a compile has a fixed place the agent reads): every call writes its full result
    # to ~/weil-launcher/compile-results/<key>.txt. 2026-10-25 (attach): the compile runs in a detached runner
    # (compile_attach.py): a call cut off (tool timeout, session restart after a 429) does not stop it; the same command
    # run again attaches to it or returns its stored result at once (same files, same contents, same dependency state).
    import hashlib, random
    RES = pathlib.Path.home() / "weil-launcher" / "compile-results"; RES.mkdir(exist_ok=True)
    h = hashlib.sha256()
    for f in sorted(str(pathlib.Path(x).resolve()) for x in fs):
        h.update(f.encode() + b"\0")
        try: h.update(pathlib.Path(f).read_bytes())
        except OSError: pass
    key = h.hexdigest()[:24]; resf = RES / f"{key}.txt"
    CL = pathlib.Path.home() / "weil-launcher" / "lcompile-calls.log"; _t_call = time.time()
    def _cl(ev, extra=""):
        try:
            with open(CL, "a") as fh: fh.write(f"{time.strftime('%F %T')} {ev} pid={os.getpid()} ppid={os.getppid()} key={key} "
                                              f"sb={lean_root(pathlib.Path(fs[0]).resolve()).parent if lean_root(pathlib.Path(fs[0]).resolve()) else '-'} "
                                              f"files={len(fs)} {extra}\n")
        except OSError: pass
    if not os.environ.get("LCOMPILE_DETACHED"):
        # 2026-10-25 (fairq): the call itself runs detached (setsid) and writes the result file; this process only waits
        # for that file and prints it. A worker session killed by a 429 restart, or a tool call cut off, kills only this
        # waiter: the result file still appears, and `cat` of it, or the same command again, gets it.
        print(f"[compile result file: {resf} -- the compile goes on even if this command is cut off; the file says PENDING "
              f"until the result is in. To get the result: run the same command again (it waits for this same compile, no new "
              f"job), or `cat` that file once it no longer says PENDING]", flush=True)
        try:
            if not resf.exists() or resf.read_text().startswith("PENDING"):
                _t = RES / f"{key}.{os.getpid()}.part"
                _t.write_text(f"PENDING: the compile of these files started at {time.strftime('%F %T')} and is still running or "
                              f"queued; this file is replaced by its result. Run the same command again to wait for it.\n")
                _t.rename(resf)
        except OSError: pass
        _cl("call")
        _ch = subprocess.Popen([sys.executable, str(pathlib.Path(__file__).resolve()), *sys.argv[1:]], stdin=subprocess.DEVNULL,
                               stdout=subprocess.DEVNULL, stderr=open(RES / f"{key}.detached.err", "a"), start_new_session=True,
                               env=dict(os.environ, LCOMPILE_DETACHED=str(_t_call)))
        while _ch.poll() is None: time.sleep(1)
        try: full = resf.read_text()
        except OSError: full = ""
        if full.startswith("PENDING") or not full:
            full = (f"compile tool fault: the compile process ended without writing its result (exit {_ch.returncode}); "
                    f"see {RES / (key + '.detached.err')}\n[exit code 2: NOT compiled]\n")
        try:
            if not (RES / f"{key}.detached.err").stat().st_size: (RES / f"{key}.detached.err").unlink()
        except OSError: pass
        m = re.search(r"\[exit code (-?\d+):", full); rc = int(m.group(1)) if m else 2
        _cl("shown", f"rc={rc} secs={time.time() - _t_call:.0f}")
        txt = full if len(full) <= 24000 else (full[:6000] + f"\n... [{len(full) - 24000} characters omitted here; the whole output is in {resf}] ...\n" + full[-18000:])
        print(txt, end=""); sys.exit(rc)
    if random.random() < 0.02:
        for x in RES.iterdir():
            try:
                if time.time() - x.stat().st_mtime > 86400:
                    if x.is_dir():
                        import shutil; shutil.rmtree(x, ignore_errors=True)
                    else: x.unlink()
            except OSError: pass
    # (detached part) ~/weil-launcher/lcompile-calls.log: call/shown by the waiter, start/printed by this process
    _cl("start")
    if len(fs) > 1: rc, out, _ = run_set(fs)
    else: rc, out = run(fs[0])
    _cl("printed", f"rc={rc} secs={time.time() - _t_call:.0f}")
    # 2026-10-26: debug dumps (expression traces) made single results 600 MB and filled the disk; keep head and tail
    if len(out) > 4_000_000:
        out = out[:1_000_000] + f"\n... [{len(out) - 4_000_000} characters of output omitted: over 4 MB] ...\n" + out[-3_000_000:]
    full = notice() + out + "\n" + f"[exit code {rc}: {'compiled' if rc == 0 else 'NOT compiled'}]\n"
    try:
        tmp = RES / f"{key}.{os.getpid()}.part"; tmp.write_text(full); tmp.rename(resf)
    except OSError: pass
    sys.exit(rc)   # the waiter prints the result file
