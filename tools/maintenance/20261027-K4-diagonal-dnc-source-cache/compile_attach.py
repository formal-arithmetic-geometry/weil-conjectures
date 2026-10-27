#!/usr/bin/env python3
"""One compile request in flight per task, results that always reach the worker (2026-10-25, the human: "the real
problem is results not getting back to the worker, so workers recompile the same thing several times").

A compile call (lcompile.py, scompile.py, and the compiles inside deliver3.py / deliver2.py) goes through attach():

  task     the files of the call (paths, probe or not, delivery or not). At most one request per task is in flight.
  content  the task plus the exact source texts (and the probe). Identical content while a request is pending:
           attach to it and get its result (no second job). Different content: the new request replaces the old one;
           the old runner cancels its queued job, or lets a running one finish and discards it.
  dep      the dependency state: the published build stamp and the sandbox's own compiled modules. Same content and
           same dep within 6 h: the stored result is returned at once.

The compile itself runs in a RUNNER, a detached process (its own session, setsid), not in the caller. A caller killed by
a tool timeout or by a session restart after a 429 does not kill the compile: running the same command again attaches
to the runner, or returns its stored result. A runner never gives up while its job is wanted; it withdraws the job only
when the request was replaced (same files, new content) or its sandbox is gone (the item ended): spec["alive_paths"]. Files: ~/weil-launcher/compile-results/ (cleaned after 24 h), log
~/weil-launcher/compile-attach.log (events new/attach/cached/superseded/done)."""
import hashlib, importlib.util, json, os, pathlib, subprocess, sys, threading, time
H = pathlib.Path.home()
RES = H / "weil-launcher" / "compile-results"
LOG = H / "weil-launcher" / "compile-attach.log"
STAMP = H / "weil-conjectures-sheaf-shared" / "local" / "builds" / "published"
FRESH = 6 * 3600
RUNNER_GRACE = float(os.environ.get("COMPILE_RUNNER_GRACE", "1800"))
DIRECT = "COMPILE_ATTACH_DIRECT"


def log(*a):
    try:
        with open(LOG, "a") as f: f.write(time.strftime("%F %T ") + " ".join(map(str, a)) + "\n")
    except OSError:
        pass


def digest(*parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else str(p).encode()); h.update(b"\0")
    return h.hexdigest()[:24]


def published_stamp():
    try: return STAMP.read_text().strip()
    except OSError: return "?"


def _alive(pid, t0=0.0):
    """The runner `pid` (started at t0) is running. Right after Popen the child may not have exec'd yet and still shows
    its parent's command line: within 60 s of t0 any live process with that pid counts (2026-10-25: that window made
    attachers think the runner dead and start duplicates)."""
    try:
        st = pathlib.Path(f"/proc/{pid}/stat").read_text()
        if st.split(") ")[1].startswith("Z"): return False
        if "compile_attach" in pathlib.Path(f"/proc/{pid}/cmdline").read_bytes().decode(errors="replace"): return True
        return time.time() - t0 < 60
    except (OSError, IndexError):
        return False


def _read(p):
    try: return p.read_text()
    except OSError: return None


def _write(p, text):
    tmp = p.with_name(p.name + f".{os.getpid()}.part"); tmp.write_text(text); tmp.rename(p)


def attach(kind, task, content, dep, spec, sources, cacheable=lambda r: True, valid=lambda r: True, prio=False):
    """Return the result of the compile described by `spec` (run by a runner, see the module doc).
    kind: 'l' (lcompile) or 's' (scompile). sources: {path: bytes}, the snapshot the runner compiles.
    cacheable(result): may this result be reused for the same content and dep. valid(result): may a stored result be
    returned now (e.g. the compiled modules it wrote still exist)."""
    RES.mkdir(exist_ok=True)
    ck = f"{kind}{content}"; run = RES / f"{ck}{'.p' if prio else ''}.run"; last = RES / f"{ck}.last.json"
    cache = RES / f"{ck}-{dep}.json"; taskf = RES / f"task-{kind}{task}"; waitf = RES / f"{ck}.wait"
    started = None
    while True:
        waitf.touch()
        txt = _read(run) or ""
        pid, _, t = txt.partition(" ")
        try: tt = float(t or 0)
        except ValueError: tt = 0.0
        live = (pid.isdigit() and _alive(int(pid), tt)) or (pid == "starting" and time.time() - tt < 60)
        if live:
            if started is None and pid.isdigit():
                started = tt; log("attach", ck, "runner", pid, spec.get("label", ""))
            time.sleep(2); continue
        if started is not None:
            r = _result(last, started)
            if r is not None: return _unwrap(r)
            started = None   # the runner ended without a result: start another one
        try:
            if time.time() - cache.stat().st_mtime < FRESH:
                r = json.loads(cache.read_text())
                if valid(r["result"]): log("cached", ck, spec.get("label", "")); return r["result"]
        except (OSError, ValueError, KeyError):
            pass
        if txt:
            try:
                if run.read_text() == txt: run.unlink()   # a dead runner's run file
            except OSError:
                pass
        try:
            fd = os.open(run, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError:
            time.sleep(1); continue
        t0 = time.time()
        os.write(fd, f"starting {t0}".encode()); os.close(fd)
        _write(taskf, ck)   # the newest request of this task; older runners of the task see it and give way
        src = RES / f"{ck}.src"; src.mkdir(exist_ok=True)
        names = {}
        for i, (p, b) in enumerate(sorted(sources.items())):
            (src / str(i)).write_bytes(b); names[p] = str(src / str(i))
        sp = RES / f"{ck}.spec.json"
        _write(sp, json.dumps(dict(spec, ck=ck, task=f"{kind}{task}", dep=dep, sources=names, run=str(run), prio=prio,
                                   cache=str(cache), last=str(last), waitf=str(waitf), t0=t0)))
        try:
            p = subprocess.Popen([sys.executable, str(pathlib.Path(__file__).resolve()), "--runner", str(sp)],
                                 stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=open(RES / f"{ck}.err", "a"),
                                 start_new_session=True, env={k: v for k, v in os.environ.items() if k != DIRECT})
        except OSError:
            run.unlink(missing_ok=True); raise
        _write(run, f"{p.pid} {t0}"); started = t0
        log("new", ck, "runner", p.pid, spec.get("label", ""))


def _result(last, started):
    try:
        r = json.loads(last.read_text())
        if started is None or r.get("t0", 0) >= started - 1: return r
    except (OSError, ValueError):
        pass
    return None


def _unwrap(r):
    if r.get("superseded"):
        return {"superseded": True, "at": r.get("at")}
    return r["result"]


def is_superseded(spec):
    return _read(pathlib.Path(spec["run"]).parent / f"task-{spec['task']}") not in (None, spec["ck"])


def runner(sp):
    spec = json.loads(pathlib.Path(sp).read_text())
    os.environ[DIRECT] = "1"
    if spec.get("prio"): os.environ["LCOMPILE_PRIO"] = "1"
    m = importlib.util.spec_from_file_location(spec["module_name"], spec["module"])
    mod = importlib.util.module_from_spec(m); sys.modules[spec["module_name"]] = mod; m.loader.exec_module(mod)
    last, cache, waitf, run = (pathlib.Path(spec[k]) for k in ("last", "cache", "waitf", "run"))
    sources = {p: pathlib.Path(f).read_bytes() for p, f in spec["sources"].items()}
    done = threading.Event()

    def finish_superseded(why):
        try:
            if hasattr(mod, "cancel"): mod.cancel()
        except Exception:
            pass
        _write(last, json.dumps({"superseded": True, "at": time.time(), "t0": spec["t0"], "why": why}))
        log(why, spec["ck"], spec.get("label", ""))
        try:
            if run.read_text().split(" ")[0] == str(os.getpid()): run.unlink()
        except OSError:
            pass
        _cleanup(spec); os._exit(0)

    def watch():
        while not done.wait(5):
            if is_superseded(spec): finish_superseded("superseded")
            ap = spec.get("alive_paths") or []
            if ap and not any(os.path.exists(x) for x in ap): finish_superseded("sandbox-gone")
    threading.Thread(target=watch, daemon=True).start()
    t = time.time()
    try:
        result = getattr(mod, spec["func"])(spec["args"], sources)
    except Exception as e:
        result = None; log("runner-error", spec["ck"], type(e).__name__, str(e)[:200])
    done.set()
    if result is None:
        result = spec.get("fail_result")
    out = {"result": result, "t0": spec["t0"], "t1": time.time(), "dep": spec["dep"]}
    _write(last, json.dumps(out))
    try:
        if result is not None and getattr(mod, "cacheable", lambda r: True)(result): _write(cache, json.dumps(out))
    except OSError:
        pass
    log("done", spec["ck"], f"{time.time() - t:.0f}s", spec.get("label", ""))
    try:
        if run.read_text().split(" ")[0] == str(os.getpid()): run.unlink()
    except OSError:
        pass
    _cleanup(spec)


def _cleanup(spec):
    import shutil
    d = pathlib.Path(spec["run"]).parent
    shutil.rmtree(d / f"{spec['ck']}.src", ignore_errors=True)
    for x in (f"{spec['ck']}.spec.json", f"{spec['ck']}.err"):
        try:
            p = d / x
            if x.endswith(".err") and p.stat().st_size: continue
            p.unlink()
        except OSError:
            pass


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--runner":
        runner(sys.argv[2])
    else:
        raise SystemExit(__doc__)
