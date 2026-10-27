#!/usr/bin/env python3
"""Remote compile of a whole lcompile call (one file or a set) for the Codex workers (2026-10-17: stage-3 worker
compiles move to this server). stdin: a gzip tar with manifest.json, the sources under lean/ and the sandbox's compiled
modules under .lbuild/. Compiles the jobs in the given order in a scratch directory against the published build of the
live repository, at nice 10. There is no request admission limit: workers must receive
compiler results even when other requests are active. stdout: a gzip tar with result.json and, for each job that
writes its compiled module (out), the files written to .lbuild/. Exit 75 (nothing on stdout) only when the published
build stays unavailable for more than 60 s. The caller retries on the server.
Committed repository imports absent from that build are compiled first into this
request's private overlay; they never modify the published build."""
import fcntl, io, json, os, pathlib, re, shutil, subprocess, sys, tarfile, tempfile, time
H = pathlib.Path.home(); REPO = H / "weil-conjectures-sheaf"; LEAN = REPO / "lean"
LEANBIN = str(H / ".elan/bin/lean")

def _pdeathsig():
    """2026-10-21: a Lean child dies with this call (SIGTERM on parent death). Calls whose worker had died (OOM-killed or
    stopped deliveries on the Codex machine) left orphaned Lean processes burning a core each for minutes (36 at 19:56)."""
    import ctypes, signal as _sig
    try:
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, _sig.SIGTERM, 0, 0, 0)   # PR_SET_PDEATHSIG
    except Exception:   # noqa: BLE001
        pass
    # 2026-10-26 (the human): PR_SET_THP_DISABLE (prctl 41) for the Lean child, inherited across exec. Lean's heap is
    # madvised for huge pages, and every fault then ran synchronous compaction (92-99% failed), which showed as
    # memory pressure (PSI ~45%) that kept the slot governors from adding slots. Fail-safe: the compile runs anyway.
    try:
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(41, 1, 0, 0, 0)   # PR_SET_THP_DISABLE
    except Exception:   # noqa: BLE001
        pass


n = 0
while (REPO / "local" / "PUBLISHING").exists():
    if n >= 30: sys.exit(75)
    time.sleep(2); n += 1
data = sys.stdin.buffer.read()
# 2026-10-21 (the human): at most SHEAF_COMPILE_SLOTS (40) calls compile at once; the others wait for a slot (a call
# never fails for this, it only answers later; after 9 min of waiting it answers 75 and the caller retries). 80
# concurrent single-file compiles had saturated the 80 cores and starved the global build, the landings and the reviews.
_SLOTS = int(os.environ.get("SHEAF_COMPILE_SLOTS", "18"))   # the human, 2026-10-22: at most 24 single-file compiles at once (18 + 6 priority)
_CAP = REPO / "local" / "compile-slots.cap"
def _slots():
    """2026-10-24 (the human): the ordinary slot count follows the machine load (95-100% of the cores busy); it is
    written by ~/cc1/slot-governor.py and read again on every wait round."""
    try:
        return max(1, int(_CAP.read_text()))
    except (OSError, ValueError):
        return _SLOTS
_slot_fh = None
_sd = REPO / "local" / "compile-slots"; _sd.mkdir(parents=True, exist_ok=True)
# 2026-10-22 (the human: the quarantine roots are fixed too slowly): a call compiling a rework or retire module
# (coord/rework.tsv, coord/retire-items.tsv) is a root everything else waits for; it has SHEAF_COMPILE_PRIO_SLOTS (8)
# slots of its own, tried first, and falls back to the ordinary slots
def _prio_call(blob):
    try:
        import tarfile, io, json as _json
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:*") as tf:
            m = None
            for ti in tf.getmembers():
                if ti.name.rstrip("/").endswith("manifest.json"):
                    m = _json.load(tf.extractfile(ti)); break
        if not m:
            return False
        mods = {str(j.get("rel", "")).removesuffix(".lean").replace("/", ".") for j in m.get("jobs", [])}
        listed = set()
        for tsv, col in (("rework.tsv", 0), ("retire-items.tsv", 2)):
            for l in (REPO / "coord" / tsv).read_text(errors="ignore").splitlines():
                c = l.split("\t")
                if l.strip() and not l.startswith("#") and len(c) > col:
                    listed.add(c[col])
        return bool(mods & listed)
    except Exception:
        return False
_PRIO = _prio_call(data)
_PSLOTS = int(os.environ.get("SHEAF_COMPILE_PRIO_SLOTS", "6"))
_pd = REPO / "local" / "compile-slots-prio"; _pd.mkdir(parents=True, exist_ok=True)
_t0 = time.time()
# 2026-10-22 (the human: calls expired although 40 slots should serve them): the slot wait was a free-for-all poll, so a
# waiter could starve past the caller's patience while newer calls got slots. Waiters now take a ticket and only the
# oldest live tickets (as many as there are slots in their pool) may try the slots: first come, first served.
_qd = REPO / "local" / "compile-queue"; _qd.mkdir(parents=True, exist_ok=True)
_ticket = _qd / f"{time.time_ns():020d}-{os.getpid()}"
_ticket.write_text("p" if _PRIO else "n")
import atexit; atexit.register(lambda: _ticket.unlink(missing_ok=True))
def _my_turn():
    """True when at most (slots - 1) live tickets of my pool are older than mine; dead owners' tickets are removed."""
    older = 0
    for t in sorted(_qd.iterdir()):
        if t.name >= _ticket.name:
            break
        try:
            pid = int(t.name.rsplit("-", 1)[1])
            os.kill(pid, 0)
        except (ValueError, ProcessLookupError, PermissionError):
            t.unlink(missing_ok=True); continue
        try:
            kind = t.read_text()
        except OSError:
            continue
        if _PRIO and kind == "p":
            older += 1
        elif not _PRIO:
            older += 1
    return older < (_PSLOTS if _PRIO else _slots())
# 2026-10-23: a caller over ssh that gave up (its ssh session ended, this process was reparented) no longer waits in
# the queue: half of 674 waiting calls had no caller left and would have compiled for nobody (queue 639, timeouts)
_ppid0 = os.getppid()
def _caller_gone():
    return os.getppid() != _ppid0
while _slot_fh is None:
    if _caller_gone():
        sys.exit(141)
    if not _my_turn():
        if time.time() - _t0 > 540:
            sys.exit(75)
        time.sleep(3); continue
    _pools = ([(_pd, _PSLOTS)] if _PRIO else []) + [(_sd, _slots())]
    for _dir, _cnt in _pools:
        for _i in range(_cnt):
            _f = open(_dir / f"{_i}.lock", "a")
            try:
                fcntl.flock(_f, fcntl.LOCK_EX | fcntl.LOCK_NB); _slot_fh = _f; break
            except OSError:
                _f.close()
        if _slot_fh is not None:
            break
    if _slot_fh is None:
        if time.time() - _t0 > 540:
            sys.exit(75)
        time.sleep(3)
_ticket.unlink(missing_ok=True)
def watch_caller():
    """2026-10-18 (waste): a Codex worker that gave up (ssh closed) left its call compiling for nobody. A call started by
    sshd whose result pipe has no reader any more (POLLERR on stdout) kills its Lean children, removes its scratch
    directory and exits. Local callers are never watched."""
    import select, signal, threading, stat
    try:
        if not pathlib.Path(f"/proc/{os.getppid()}/comm").read_text().startswith("sshd") or "SSH_CONNECTION" not in os.environ:
            return
        if not stat.S_ISFIFO(os.fstat(1).st_mode): return
    except OSError:
        return
    poller = select.poll(); poller.register(1, select.POLLERR)
    def loop():
        while True:
            if any(ev & select.POLLERR for _, ev in poller.poll(5000)):
                kids = {}
                for q in pathlib.Path("/proc").iterdir():
                    if q.name.isdigit():
                        try: kids.setdefault(int((q / "stat").read_text().rsplit(")", 1)[1].split()[1]), []).append(int(q.name))
                        except (OSError, ValueError, IndexError): pass
                todo = [os.getpid()]
                while todo:
                    for c in kids.get(todo.pop(), []):
                        todo.append(c)
                        try: os.kill(c, signal.SIGKILL)
                        except OSError: pass
                try:
                    with open(H / "cc1" / "rset-callergone.log", "a") as lf: lf.write(time.strftime("%F %T") + f" {os.getpid()}\n")
                except OSError: pass
                try: shutil.rmtree(td, ignore_errors=True)
                except NameError: pass
                os._exit(141)
    threading.Thread(target=loop, daemon=True).start()
watch_caller()
base = H / "cc1" / "rset-tmp"; base.mkdir(exist_ok=True)
td = pathlib.Path(tempfile.mkdtemp(prefix="c-", dir=base)); root = td / "lean"; lb = td / ".lbuild"
def safe(name):
    p = pathlib.PurePosixPath(name)
    return not p.is_absolute() and ".." not in p.parts
try:
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as t:
        for m in t.getmembers():
            if not m.isfile() or not safe(m.name): continue
            dst = td / m.name; dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(t.extractfile(m).read())
    man = json.loads((td / "manifest.json").read_text()); lb.mkdir(exist_ok=True); root.mkdir(exist_ok=True)
    def opts():
        out, on = [], False
        for l in (LEAN / "lakefile.toml").read_text().split("\n"):
            if l.startswith("[leanOptions]"): on = True; continue
            if l.startswith("["): on = False
            m = re.match(r"([A-Za-z][\w.]*)\s*=\s*([^#]*)", l) if on else None
            if m: out.append(f"-D{m.group(1)}={m.group(2).strip().strip(chr(34))}")
        return out
    OPTS = opts()
    LP = ":".join([str(LEAN / ".lake/build/lib/lean")] + sorted(str(x) for x in (LEAN / ".lake/packages").glob("*/.lake/build/lib/lean")))
    def arts():
        """as lcompile.local_artifacts: every compiled module in the scratch .lbuild, with its companions"""
        a = {}
        for p in lb.rglob("*.olean"):
            if p.is_symlink(): continue
            ol = [str(p)]
            for s in (".olean.server", ".olean.private"):
                q = p.with_suffix(s)
                if not q.is_file(): break
                ol.append(str(q))
            ir = []
            for s in (".ir.sig", ".ir"):
                q = p.with_suffix(s)
                if not q.is_file(): break
                ir.append(str(q))
            a[".".join(p.relative_to(lb).with_suffix("").parts)] = [ol, ir]
        return a
    # 2026-10-17 (cpu): shared result cache across calls. After an upstream sync many workers send the same chain of
    # 400+ unchanged-source modules at once (10 concurrent calls compiling identical sets were seen); a job whose
    # source, options and whole import closure (Merkle over the olean files it would load) match a finished job reuses
    # its outputs, and a per-key lock makes a concurrent identical job wait for the first instead of compiling twice.
    import hashlib
    CACHE = H / "cc1" / "rset-cache"; PUB = LEAN / ".lake/build/lib/lean"
    _SCAN = None
    def header_imports(path):
        # Share the comment-aware parser used by source gates. Lean permits a
        # public import to wrap before its module name; line scanning stopped
        # there and silently lost that dependency and all following imports.
        # 2026-10-27: the same parser, memoized by text in tools/leanindex.py's text cache (import_cycles._memo_imports,
        # also used by the lander's import graph): parsing the ~10000 files of a closure took 20-65 s of one core
        global _SCAN
        if _SCAN is None:
            import import_cycles
            _SCAN = import_cycles._memo_imports()
        try:
            return sorted(_SCAN(path.read_text(errors="ignore")))
        except OSError:
            return []
    # 2026-10-27: the closure keys are kept across the jobs of one call. Clearing them for every job re-read and parsed
    # the whole import closure (~10000 modules, ~20 s of Python) per compiled job while holding a compile slot (a call
    # with 46 delivered modules spent 15 min before its first compile). Only a key whose closure reaches a module that
    # this call compiles itself (_VOL: its .lbuild object appears or changes between jobs), or an import cycle, can
    # change between jobs; those are dropped before each job, the others are the same values as before.
    _fh = {}; _mk = {}; _mv = {}; _VOL = set()
    def fhash(f):
        if f not in _fh: _fh[f] = hashlib.sha256(f.read_bytes()).hexdigest()
        return _fh[f]
    def mkey(mod):
        if mod in _mk: return _mk[mod]
        _mk[mod] = "cycle"
        rel = pathlib.PurePosixPath(*mod.split("."))
        lo = lb / rel.with_suffix(".olean"); po = PUB / rel.with_suffix(".olean")
        if lo.exists():
            ident = "L" + fhash(lo); src = root / rel.with_suffix(".lean")
            if not src.exists(): src = LEAN / rel.with_suffix(".lean")
        elif po.exists():
            st = po.stat(); ident = f"P{st.st_mtime_ns}:{st.st_size}"; src = LEAN / rel.with_suffix(".lean")
        else:
            _mk[mod] = "X" + mod; _mv[mod] = mod in _VOL; return _mk[mod]
        vol, parts = mod in _VOL, []
        for i in header_imports(src):
            parts.append(mkey(i)); vol = vol or _mv.get(i, True)   # no flag yet: an import cycle in progress
        _mk[mod] = hashlib.sha256((mod + ident + "|".join(parts)).encode()).hexdigest(); _mv[mod] = vol
        return _mk[mod]
    def job_key(j, f, cmd):
        for m in [m for m in _mk if _mv.get(m, True)]:
            del _mk[m]; _mv.pop(m, None)
        h = hashlib.sha256(json.dumps([os.path.realpath(LEANBIN), cmd[3:], j["rel"]]).encode())
        h.update(f.read_bytes())
        for i in header_imports(f): h.update(mkey(i).encode())
        return h.hexdigest()
    import random
    if random.random() < 0.02 and CACHE.is_dir():   # entries unused for a day are dropped
        for x in CACHE.iterdir():
            try:
                if time.time() - x.stat().st_mtime > 86400:
                    shutil.rmtree(x) if x.is_dir() else x.unlink()
            except OSError: pass
    timeout = int(man.get("timeout", 60)); results = []; outputs = []
    # 2026-10-26 (the human): `timeout` (the manifest's, 60 s) stays the ACCEPTANCE limit: a requested file whose compile
    # takes longer is NOT accepted (exit 124, never cached). Lean itself is stopped only at RUN_LIMIT (300 s), so the
    # declaration the file was slow on finishes and its messages and timings reach the worker (at 60 s Lean had printed
    # nothing for it: 48% of worker compiles ended in a bare "timeout after 60 s").
    RUN_LIMIT = max(timeout, int(os.environ.get("SHEAF_FILE_RUN_LIMIT", "120")))
    def over_note(dt):
        return (f"NOT ACCEPTED: this compile took {dt:.0f} s > {timeout} s, the limit for one file (every file must compile "
                f"alone within {timeout} s). The compile was allowed to run up to {RUN_LIMIT} s only so that the slow "
                "declarations finish and report: the messages above show them (to see where the time goes, add "
                "`set_option profiler true` with `set_option profiler.threshold 100` at the top of the file while debugging, "
                "and remove them before delivering). The cause is usually a definition that is expensive to unfold; change it, not the limit.\n")
    for j in man["jobs"]:
        if not safe(j["rel"]) or pathlib.PurePosixPath(j["rel"]).suffix != ".lean":
            raise SystemExit("bad path")
    # A landed module can be newer than the last green publication. Compile its
    # real committed sources privately, using the same per-file limit and cache.
    # Never copy unverified objects from the global build tree into publication.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    from remote_compile_dependencies import missing_dependencies, compile_order, DependencySourceError
    try:
        dependencies = missing_dependencies(man["jobs"], root, lb, PUB, LEAN, REPO, header_imports)
        scheduled = compile_order(man["jobs"], dependencies, root, header_imports)
        _VOL.update(str(pathlib.PurePosixPath(j["rel"]).with_suffix("")).replace("/", ".") for j in scheduled)
    except (DependencySourceError, OSError, subprocess.CalledProcessError) as exc:
        dependencies = []
        results = [{"rel": j["rel"], "rc": 1, "out": f"Dependency source unavailable: {exc}\n",
                    "secs": 0, "arts": False} for j in man["jobs"]]
    dependency_notes = []
    for j in ([] if results else scheduled):
        rel = pathlib.PurePosixPath(j["rel"])
        if not safe(j["rel"]) or rel.suffix != ".lean": raise SystemExit("bad path")
        f = root / rel; t0 = time.time()
        cmd = ["nice", "-n", "19", LEANBIN, "-j1", *OPTS]   # -j1: one core per single-file compile (the human, 2026-10-22) + ([] if j.get("upstream") else ["-DautoImplicit=false"])
        src = f
        if j.get("probe"):
            src = f.with_name(f.stem + "__probe.lean"); src.write_text(f.read_text() + j["probe"])
        else: cmd += ["-R", str(root)]
        if j.get("out") and not j.get("probe"):
            o = lb / rel.with_suffix(".olean"); o.parent.mkdir(parents=True, exist_ok=True)
            for x in o.parent.glob(o.stem + ".*"): x.unlink()
            cmd += ["-o", str(o), "-i", str(o.with_suffix(".ilean"))]
        a = arts(); setup = None
        if a:
            setup = td / "setup.json"
            setup.write_text(json.dumps({"name": ".".join(src.relative_to(root).with_suffix("").parts), "isModule": False,
                                         "importArts": a, "dynlibs": [], "plugins": [], "options": {}}))
            cmd += ["--setup", str(setup)]
        key = ckf = None; hit = False
        if j.get("out") and not j.get("probe"):
            try:
                key = job_key(j, f, [x for x in cmd if not x.startswith(str(td))])
                CACHE.mkdir(exist_ok=True); ckf = open(CACHE / (key + ".lock"), "w"); fcntl.flock(ckf, fcntl.LOCK_EX)
                cd = CACHE / key
                if (cd / "result.json").is_file():
                    o = lb / rel.with_suffix(".olean")
                    for x in cd.iterdir():
                        if x.name != "result.json": shutil.copyfile(x, o.parent / x.name)
                    rc, out = 0, json.loads((cd / "result.json").read_text())["out"]; hit = True
                    os.utime(cd)
            except Exception:   # noqa: BLE001  (the cache never fails a compile)
                key = None
        try:
            if not hit:
                # 2026-10-25: stdbuf makes Lean flush each message line, so a compile stopped at the limit still
                # returns the messages printed before the stop (piped, Lean held them all in its buffer)
                t_run = time.time()
                p = subprocess.run(["stdbuf", "-oL", "-eL"] + cmd + [str(src)], preexec_fn=_pdeathsig, cwd=str(LEAN), env=dict(os.environ, LEAN_PATH=LP, LEAN_NUM_THREADS="1"),
                                   capture_output=True, text=True, timeout=RUN_LIMIT)
                rc, out = p.returncode, p.stdout + p.stderr
                if not j.get("dependency") and time.time() - t_run > timeout:   # finished, but too slow: not accepted
                    rc = rc or 124
                    out = out.rstrip("\n") + "\n" + over_note(time.time() - t_run)
                if key and rc == 0:
                    try:
                        o = lb / rel.with_suffix(".olean"); tmp = CACHE / f"{key}.{os.getpid()}.tmp"; tmp.mkdir()
                        for x in o.parent.glob(o.stem + ".*"):
                            if x.is_file(): shutil.copyfile(x, tmp / x.name)
                        (tmp / "result.json").write_text(json.dumps({"out": out, "rel": j["rel"]}))
                        os.rename(tmp, CACHE / key)
                    except OSError:
                        shutil.rmtree(CACHE / f"{key}.{os.getpid()}.tmp", ignore_errors=True)
        except subprocess.TimeoutExpired as exc:
            # 2026-10-25: keep what Lean printed before the limit (errors, goals of earlier declarations); a
            # timeout with no message at all keeps out=None and the caller's standard text
            partial = "".join(v.decode(errors="replace") if isinstance(v, bytes) else (v or "")
                              for v in (exc.stdout, exc.stderr))
            rc = 124
            out = ((partial.rstrip("\n") + "\n") if partial.strip() else "") + (
                f"NOT ACCEPTED: stopped after {RUN_LIMIT} s, the longest a compile may run (every file must compile alone "
                f"within {timeout} s): the fault is usually a definition that is expensive to unfold, not the limit (the "
                "messages above are those Lean printed before it was stopped; the slow part comes after the last "
                "declaration they report)\n")
        finally:
            if j.get("probe"): src.unlink(missing_ok=True)
            if ckf: ckf.close()
        if j.get("dependency"):
            if rc:
                diagnostic = out if out is not None else f"timeout after {RUN_LIMIT} s\n"
                diagnostic = (f"Dependency {j['dependency']} from {j['source_commit']} "
                              f"failed in the private compile overlay:\n{diagnostic}")
                results = [{"rel": requested["rel"], "rc": rc, "out": diagnostic,
                            "secs": round(time.time() - t0, 1), "arts": bool(a)}
                           for requested in man["jobs"]]
                break
            dependency_notes.append(
                f"Compiled unpublished dependency {j['dependency']} from {j['source_commit']} "
                f"in the private overlay{' (cache)' if hit else ''}.\n" + out)
            continue
        if out is not None and dependency_notes:
            out = "".join(dependency_notes) + out
            dependency_notes = []
        results.append({"rel": j["rel"], "rc": rc, "out": out, "secs": round(time.time() - t0, 1), "arts": bool(a)})
        if j.get("out") and not j.get("probe"):
            o = lb / rel.with_suffix(".olean")
            outputs += [x for x in o.parent.glob(o.stem + ".*") if x.is_file()]
        if rc and man.get("stop_on_fail"): break
    # The caller associates results by manifest position, even when source
    # dependencies required compiling its jobs in a different order.
    by_rel = {result["rel"]: result for result in results}
    if man.get("stop_on_fail") and any(result["rc"] for result in results):
        failure = next(result for result in results if result["rc"])
        for job in man["jobs"]:
            by_rel.setdefault(job["rel"], {
                "rel": job["rel"], "rc": 1, "secs": 0, "arts": False,
                "out": f"NOT compiled: the request stopped after {failure['rel']} failed.\n"
                       + (failure["out"] or "")})
    results = [by_rel[job["rel"]] for job in man["jobs"] if job["rel"] in by_rel]
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=3) as t:
        r = json.dumps({"td": str(td), "results": results}).encode()
        ti = tarfile.TarInfo("result.json"); ti.size = len(r); t.addfile(ti, io.BytesIO(r))
        for x in outputs: t.add(str(x), arcname=str(x.relative_to(td)))
    sys.stdout.buffer.write(buf.getvalue()); sys.stdout.buffer.flush()
finally:
    shutil.rmtree(td, ignore_errors=True)
