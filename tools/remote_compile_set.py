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
n = 0
while (REPO / "local" / "PUBLISHING").exists():
    if n >= 30: sys.exit(75)
    time.sleep(2); n += 1
data = sys.stdin.buffer.read()
# 2026-10-21 (the human): at most SHEAF_COMPILE_SLOTS (40) calls compile at once; the others wait for a slot (a call
# never fails for this, it only answers later; after 9 min of waiting it answers 75 and the caller retries). 80
# concurrent single-file compiles had saturated the 80 cores and starved the global build, the landings and the reviews.
_SLOTS = int(os.environ.get("SHEAF_COMPILE_SLOTS", "36")); _slot_fh = None
_sd = REPO / "local" / "compile-slots"; _sd.mkdir(parents=True, exist_ok=True)
_t0 = time.time()
while _slot_fh is None:
    for _i in range(_SLOTS):
        _f = open(_sd / f"{_i}.lock", "a")
        try:
            fcntl.flock(_f, fcntl.LOCK_EX | fcntl.LOCK_NB); _slot_fh = _f; break
        except OSError:
            _f.close()
    if _slot_fh is None:
        if time.time() - _t0 > 540:
            sys.exit(75)
        time.sleep(3)
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
    IMP = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")
    def header_imports(path):
        try: t = path.read_text(errors="ignore")
        except OSError: return []
        t = re.sub(r"/-.*?-/", "", t, flags=re.S); out = []
        for l in t.split("\n"):
            l = l.split("--", 1)[0].strip()
            if not l or l in ("module", "prelude"): continue
            m = IMP.match(l)
            if not m: break
            out.append(m.group(1))
        return out
    _fh = {}; _mk = {}
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
            _mk[mod] = "X" + mod; return _mk[mod]
        _mk[mod] = hashlib.sha256((mod + ident + "|".join(mkey(i) for i in header_imports(src))).encode()).hexdigest()
        return _mk[mod]
    def job_key(j, f, cmd):
        _mk.clear()
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
    for j in man["jobs"]:
        if not safe(j["rel"]) or pathlib.PurePosixPath(j["rel"]).suffix != ".lean":
            raise SystemExit("bad path")
    # A landed module can be newer than the last green publication. Compile its
    # real committed sources privately, using the same per-file limit and cache.
    # Never copy unverified objects from the global build tree into publication.
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    from remote_compile_dependencies import missing_dependencies, DependencySourceError
    try:
        dependencies = missing_dependencies(man["jobs"], root, lb, PUB, LEAN, REPO, header_imports)
    except (DependencySourceError, OSError, subprocess.CalledProcessError) as exc:
        dependencies = []
        results = [{"rel": j["rel"], "rc": 1, "out": f"Dependency source unavailable: {exc}\n",
                    "secs": 0, "arts": False} for j in man["jobs"]]
    dependency_notes = []
    for j in ([] if results else dependencies + man["jobs"]):
        rel = pathlib.PurePosixPath(j["rel"])
        if not safe(j["rel"]) or rel.suffix != ".lean": raise SystemExit("bad path")
        f = root / rel; t0 = time.time()
        cmd = ["nice", "-n", "19", LEANBIN, *OPTS] + ([] if j.get("upstream") else ["-DautoImplicit=false"])
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
                p = subprocess.run(cmd + [str(src)], cwd=str(LEAN), env=dict(os.environ, LEAN_PATH=LP, LEAN_NUM_THREADS="1"),
                                   capture_output=True, text=True, timeout=timeout)
                rc, out = p.returncode, p.stdout + p.stderr
                if key and rc == 0:
                    try:
                        o = lb / rel.with_suffix(".olean"); tmp = CACHE / f"{key}.{os.getpid()}.tmp"; tmp.mkdir()
                        for x in o.parent.glob(o.stem + ".*"):
                            if x.is_file(): shutil.copyfile(x, tmp / x.name)
                        (tmp / "result.json").write_text(json.dumps({"out": out, "rel": j["rel"]}))
                        os.rename(tmp, CACHE / key)
                    except OSError:
                        shutil.rmtree(CACHE / f"{key}.{os.getpid()}.tmp", ignore_errors=True)
        except subprocess.TimeoutExpired:
            rc, out = 124, None
        finally:
            if j.get("probe"): src.unlink(missing_ok=True)
            if ckf: ckf.close()
        if j.get("dependency"):
            if rc:
                diagnostic = out if out is not None else f"timeout after {timeout} s\n"
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
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=3) as t:
        r = json.dumps({"td": str(td), "results": results}).encode()
        ti = tarfile.TarInfo("result.json"); ti.size = len(r); t.addfile(ti, io.BytesIO(r))
        for x in outputs: t.add(str(x), arcname=str(x.relative_to(td)))
    sys.stdout.buffer.write(buf.getvalue()); sys.stdout.buffer.flush()
finally:
    shutil.rmtree(td, ignore_errors=True)
