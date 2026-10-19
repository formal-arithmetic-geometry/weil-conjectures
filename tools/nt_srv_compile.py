#!/usr/bin/env python3
"""2026-10-17: stage-2 compiles on the server with a persistent side overlay (server port of the launcher's
maint/s2land/nt_local_compile.py; same steps, same output, same exit codes).

Side modules (side files missing from live, plus the explicit replacements of coord/stage2-source-overrides.json, as
tools/nt_source_overlay.py selects them) are compiled once against the live published build into the content-addressed
cache ~/weil-nt-overlay/kcache/<module>/<key> and reused (2026-10-18; before, one shared ~/weil-nt-overlay/cache/.lbuild
overwritten in place). A module is recompiled only when its source or one of its direct imports changed: the key is the
source text plus, per import, the key of the side import or the mtime/size of the live olean (see kcompile).
Every call snapshots the side sources (content-addressed, ~/weil-nt-overlay/snapshots/<version>) so a landing in
progress never changes a file under a running compile. Only modules of the current snapshot are passed to Lean.

    nt_srv_compile.py                 stdin {files: {rel: text}}  -> Lean output, exit code   (as nt_local_compile.py)
    nt_srv_compile.py                 stdin a landing plan {id, modules, ...} -> receipt JSON {id, rc, out}
    nt_srv_compile.py --wire          stdin either; stdout one JSON line {rc, out} or the receipt (remote callers)
    nt_srv_compile.py --warm          compile every side module of the current snapshot into the cache (maintenance)
    nt_srv_compile.py --wire-confirm  stdin {files}: as --wire; a failure is confirmed with tools/nt_compile.py exactly
                                      as the launcher's scompile.py does (its output appended, its exit code returned)

Every Lean process: nice 19, two threads, 60 s after slot acquisition, at most NT_LCOMPILE_SLOTS at once.
"""
import fcntl, hashlib, json, os, pathlib, re, shutil, subprocess, sys, tempfile, time

TOOLS = pathlib.Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
import nt_lcompile as lc
from nt_source_overlay import load_overrides, overlay_sources

STATE = pathlib.Path(os.environ.get("NT_SRV_OVERLAY", str(pathlib.Path.home() / "weil-nt-overlay")))
CACHE = STATE / "cache"
SNAPSHOTS = STATE / "snapshots"
OVERLAY = CACHE / ".lbuild"
PUBLISHED = lc.P.parent / "local/builds/published"
IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', re.M)
ORIGINAL_ARTS = lc.local_artifacts
CURRENT = set()          # modules of the current snapshot (stale_live_clash reads it)
# 2026-10-18 (waste): every compile is content addressed. An entry ~/weil-nt-overlay/kcache/<module>/<key> holds the
# artifacts and the Lean output of one compile; the key is the module name, the kind (library or sandbox), the source
# text, the Lean options and toolchain, the side overrides' keys, and per import the key of the side/supplied module
# this call compiled or the mtime/size of the published live olean. Entries are written once (renamed into place) and
# never overwritten, so concurrent calls on different snapshots no longer delete each other's oleans (the "object file
# ... does not exist" failures that sent ~77 calls an hour into the from-scratch confirmation), a module alternating
# between two snapshot versions is not recompiled each time, and a caller's supplied module, its private importers,
# and the preliminary/library compiles of the same text share one compile across calls and within a call. A second
# caller of the same key waits on the key's lock and reads the first one's result (single flight).
CALLMAP = {}             # module -> Lean --setup artifacts of this call's version
CALLKEY = {}             # module -> content key of this call's version
CALL_START = [time.time()]
OVR = [None]             # the side overrides' keys, part of every later key
KC = STATE / "kcache"
KEY_SALT = None


def artifacts(lb):
    out = dict(CALLMAP)
    if lb and pathlib.Path(lb).is_dir():
        out.update(ORIGINAL_ARTS(lb))
    return out
lc.local_artifacts = artifacts


FAILED_IN_DELIVERED = [False]
INFRA_TEXT = ("object file", "unknown module", "No such file")


class CompileError(Exception):
    def __init__(self, rc, out):
        self.rc = rc; self.out = out


def salt():
    global KEY_SALT
    if KEY_SALT is None:
        try: tc = (lc.P / "lean-toolchain").read_text()
        except OSError: tc = ""
        KEY_SALT = json.dumps([1, lc.base_opts(), tc])
    return KEY_SALT


def key_of(module, text, kind):
    inputs = {}
    for dep in IMPORT.findall(text):
        if dep in CALLKEY: inputs[dep] = CALLKEY[dep]
        else:
            try:
                st = (lc.BUILD / (dep.replace(".", "/") + ".olean")).stat(); inputs[dep] = [st.st_mtime_ns, st.st_size]
            except OSError:
                inputs[dep] = None
    return hashlib.sha256(json.dumps([salt(), kind, module, text, inputs, OVR[0]], sort_keys=True).encode()).hexdigest()[:40]


def kcompile(module, src, kind, label, progress, output, quiet_hit=False):
    """Compile src as `module` once per content key (see above); append the output; raise CompileError on failure."""
    text = src.read_text(); k = key_of(module, text, kind)
    base = KC / module; base.mkdir(parents=True, exist_ok=True)
    entry = base / k; failf = base / (k + ".fail")
    hit = None
    with (base / (k + ".lock")).open("a") as lf:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            if progress: progress("Waiting for a concurrent compile of the same " + module)
            fcntl.flock(lf, fcntl.LOCK_EX)
        if (entry / "result.json").is_file():
            hit = json.loads((entry / "result.json").read_text())
            try: os.utime(entry)
            except OSError: pass
        elif failf.is_file():
            try:
                f = json.loads(failf.read_text())
                final = f["rc"] == 1 and not any(m in f["out"] for m in INFRA_TEXT)
                if (final and time.time() - f["t"] < 3600) or f["t"] >= CALL_START[0]:
                    hit = f
            except (OSError, ValueError, KeyError):
                pass
        if hit is None:
            if progress: progress("Compiling " + label + module + " (60 s limit after slot acquisition)")
            tmp = base / ("tmp-" + k + "-" + str(os.getpid()))
            shutil.rmtree(tmp, ignore_errors=True); tmp.mkdir()
            rc, out = lc.run(src, 60, out=tmp)
            if rc == 0:
                if kind == "sandbox":
                    for x in tmp.rglob("*"):
                        if x.is_file(): x.unlink()
                (tmp / "result.json").write_text(json.dumps({"rc": 0, "out": out, "t": time.time()}))
                tmp.rename(entry); failf.unlink(missing_ok=True)
            else:
                shutil.rmtree(tmp, ignore_errors=True)
                failf.write_text(json.dumps({"rc": rc, "out": out, "t": time.time()}))
            hit = {"rc": rc, "out": out}
            quiet_hit = False
    rc, out = hit["rc"], hit["out"]
    if not (quiet_hit and rc == 0):
        output.append(label + module + "\n" + out)
    if rc:
        FAILED_IN_DELIVERED[0] = rc == 1 and not any(m in out for m in INFRA_TEXT)
        raise CompileError(rc, "\n".join(output))
    if kind != "sandbox":
        arts = ORIGINAL_ARTS(entry)
        if module in arts: CALLMAP[module] = arts[module]
        CALLKEY[module] = k
    return rc, out


def snapshot():
    """The side overlay sources, content addressed (same version hash as parallel_land.overlay). The call holds a
    shared lock on <snapshot>/version while it runs, so prune() never removes a snapshot in use."""
    files = overlay_sources(ROOT, lc.P)
    overrides = json.dumps(sorted(rel[:-5].replace("/", ".") for rel in load_overrides(ROOT))).encode()
    h = hashlib.sha256(overrides)
    for rel, body in sorted(files.items()):
        h.update(rel.encode()); h.update(body)
    version = h.hexdigest()
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    dst = SNAPSHOTS / version
    if not dst.exists():
        tmp = pathlib.Path(tempfile.mkdtemp(dir=SNAPSHOTS, prefix="new-"))
        for rel, body in files.items():
            p = tmp / "lean" / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(body)
        (tmp / "source-overrides.json").write_bytes(overrides)
        (tmp / "version").write_text(version)
        try:
            tmp.rename(dst)
        except OSError:                       # another call wrote the same version first
            shutil.rmtree(tmp, ignore_errors=True)
    else:
        os.utime(dst)
    try:
        SNAP_LOCK.append(open(dst / "version"))
        fcntl.flock(SNAP_LOCK[-1], fcntl.LOCK_SH)
    except OSError:
        pass
    prune()
    return dst
SNAP_LOCK = []


def prune():
    """At most every 10 minutes: drop snapshots unused for an hour that no running call holds (each ~35 MB), content
    cache entries unused for 12 hours, and leftovers of killed compiles."""
    stamp = STATE / "prune.stamp"
    now = time.time()
    try:
        if now - stamp.stat().st_mtime < 600: return
    except OSError:
        pass
    stamp.touch()
    for d in SNAPSHOTS.iterdir():
        try:
            age = now - d.stat().st_mtime
            if d.name.startswith("new-"):
                if age > 3600: shutil.rmtree(d, ignore_errors=True)
                continue
            if age < 3600: continue
            with open(d / "version") as f:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)      # raises while a call holds it
                shutil.rmtree(d, ignore_errors=True)
        except OSError:
            pass
    if KC.is_dir():
        for base in KC.iterdir():
            try:
                for e in base.iterdir():
                    age = now - e.stat().st_mtime
                    if (e.name.startswith("tmp-") and age > 3600) or age > 12 * 3600:
                        shutil.rmtree(e, ignore_errors=True) if e.is_dir() else e.unlink(missing_ok=True)
            except OSError:
                pass


def run(files, progress=None, warm=False):
    os.nice(max(0, 19 - os.getpriority(os.PRIO_PROCESS, 0)))
    CALL_START[0] = time.time()
    CALLMAP.clear(); CALLKEY.clear(); OVR[0] = None
    source_root = snapshot(); sources = source_root / "lean"
    # Caller-supplied modules are source overrides: a side module that imports one is compiled against it (its key
    # carries the supplied text, so it never claims to be the side snapshot's version).
    supplied = {
        pathlib.PurePosixPath(rel).with_suffix("").as_posix().replace("/", "."): text
        for rel, text in files.items()
    }
    CURRENT.clear()
    CURRENT.update(".".join(p.relative_to(sources).with_suffix("").parts) for p in sources.rglob("*.lean"))
    CURRENT.update(supplied)
    active = set(); done = set(); output = []

    supplied_tmp = tempfile.TemporaryDirectory(prefix="nt-supplied-", dir="/dev/shm/nt-tmp")
    supplied_sources = pathlib.Path(supplied_tmp.name) / "lean"
    supplied_paths = {}
    for rel, text in files.items():
        p = supplied_sources / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        supplied_paths[pathlib.PurePosixPath(rel).with_suffix("").as_posix().replace("/", ".")] = p

    # The transitive side importers of supplied modules (labelled "private overlay" in the output, as before).
    private_modules = set(supplied)
    imports = {
        ".".join(p.relative_to(sources).with_suffix("").parts): IMPORT.findall(p.read_text())
        for p in sources.rglob("*.lean")
    }
    while True:
        affected = {m for m, deps in imports.items() if private_modules.intersection(deps)}
        if affected <= private_modules: break
        private_modules.update(affected)

    def ensure(module):
        if module in done: return
        if module in active: raise RuntimeError("side overlay import cycle: " + module)
        src = supplied_paths.get(module, sources / (module.replace(".", "/") + ".lean"))
        if not src.is_file(): return
        active.add(module); text = src.read_text()
        for dep in IMPORT.findall(text):
            ensure(dep)
        private = module in private_modules
        kcompile(module, src, "library", "private overlay " if private else "overlay ", progress, output,
                 quiet_hit=not private)
        active.remove(module); done.add(module)

    # Keep the explicit replacements available even when a published importer reaches them transitively, without
    # visiting their side sources here.
    manifest = source_root / "source-overrides.json"
    if manifest.is_file():
        for module in json.loads(manifest.read_text()):
            ensure(module)
    OVR[0] = sorted(CALLKEY.items())
    if warm:                                  # --warm: every module of the snapshot, in random order
        import random
        for module in random.sample(sorted(CURRENT), len(CURRENT)):
            try: ensure(module)
            except CompileError as exc: print(exc.out[-400:], flush=True); active.clear()
        return 0, "\n".join(output)
    for text in files.values():
        for module in IMPORT.findall(text):
            ensure(module)
    with tempfile.TemporaryDirectory(prefix="nt-local-compile-", dir="/dev/shm/nt-tmp") as tmp:
        root = pathlib.Path(tmp) / "lean"; root.mkdir(); lb = root.parent / ".lbuild"; lb.mkdir()
        paths = []
        for rel, text in files.items():
            p = root / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text); paths.append(p)
        ordered = lc.order(paths); siblings = {lc.modname(p) for p in paths}

        def check(p, kind, label):
            kcompile(lc.modname(p), p, kind, label, progress, output)
        if len(paths) > 1:
            for p in ordered:
                if not (set(IMPORT.findall(p.read_text())) & siblings): check(p, "library", "preliminary ")
        for i, p in enumerate(ordered):
            sand = root / "Sheaf/Stage2" / ("Sandbox" + str(i) + ".lean"); sand.parent.mkdir(parents=True, exist_ok=True)
            sand.write_text(p.read_text())
            check(sand, "sandbox", "sandbox ")
            check(p, "library", "library ")
    return 0, "\n".join(output)


def seed():
    """--seed (2026-10-18, once at the switch to kcache): copy every module of the current snapshot whose entry in the old
    shared cache (~/weil-nt-overlay/cache/.lbuild, one marker per module) is consistent with the current sources into
    the content-addressed cache under its new key, so the switch does not recompile the warm overlay. A module is copied
    only when its old marker matches its current text and imports and all its side imports were copied too."""
    CALL_START[0] = time.time(); CALLMAP.clear(); CALLKEY.clear(); OVR[0] = None
    source_root = snapshot(); sources = source_root / "lean"
    CURRENT.clear()
    CURRENT.update(".".join(p.relative_to(sources).with_suffix("").parts) for p in sources.rglob("*.lean"))
    good = set(); seen = {}; copied = [0]

    def visit(module):
        if module in seen: return seen[module]
        src = sources / (module.replace(".", "/") + ".lean")
        if not src.is_file(): seen[module] = None; return None
        seen[module] = False
        text = src.read_text(); deps = IMPORT.findall(text)
        ok = all(visit(d) is not False for d in deps)
        inputs = {}
        for dep in deps:
            marker_dep = CACHE / (dep + ".ok"); artifact = lc.BUILD / (dep.replace(".", "/") + ".olean")
            if dep in CURRENT and marker_dep.exists(): inputs[dep] = marker_dep.read_text()
            elif artifact.exists():
                st = artifact.stat(); inputs[dep] = [st.st_mtime_ns, st.st_size]
        k = key_of(module, text, "library"); CALLKEY[module] = k
        marker = CACHE / (module + ".ok")
        h = hashlib.sha256((text + json.dumps(inputs, sort_keys=True)).encode()).hexdigest()
        ok = ok and marker.exists() and marker.read_text() == h
        if ok:
            base = KC / module; entry = base / k
            if not entry.exists():
                with (CACHE / (module + ".lock")).open("a") as f:
                    fcntl.flock(f, fcntl.LOCK_EX)
                    if not (marker.exists() and marker.read_text() == h): ok = False
                    else:
                        rel = module.replace(".", "/")
                        files = [x for x in (OVERLAY / rel).parent.glob(pathlib.Path(rel).name + ".*")] if (OVERLAY / rel).parent.is_dir() else []
                        if not any(x.suffix == ".olean" for x in files): ok = False
                        else:
                            base.mkdir(parents=True, exist_ok=True)
                            tmp = base / ("tmp-" + k + "-" + str(os.getpid())); shutil.rmtree(tmp, ignore_errors=True)
                            (tmp / rel).parent.mkdir(parents=True)
                            for x in files: shutil.copy2(x, (tmp / rel).parent / x.name)
                            (tmp / "result.json").write_text(json.dumps({"rc": 0, "out": "(seeded from the shared overlay cache)", "t": time.time()}))
                            tmp.rename(entry); copied[0] += 1
        seen[module] = ok
        return ok

    manifest = source_root / "source-overrides.json"
    order = json.loads(manifest.read_text()) if manifest.is_file() else []
    for module in order: visit(module)
    OVR[0] = sorted(CALLKEY.items())          # as run(): the overrides and their side imports, keyed without OVR
    for module in sorted(CURRENT): visit(module)
    print(json.dumps({"modules": len(CURRENT), "consistent": sum(1 for v in seen.values() if v), "copied": copied[0]}))
    return 0


# 2026-10-17 (staleolean): an import clash "environment already contains 'X' from M", where M is a live module (not a
# module of this call's side snapshot) whose live source is newer than its published olean, is the live build lagging
# behind a merge (e.g. a module turned into a re-export), not the delivery's fault: exit INFRA_RC, never a return.
# A clash with an unchanged live module, or with a side module, stays a failure.
STALE_CLASH = re.compile(r"environment already contains '[^']+' from ([A-Za-z_][\w'.]*)")
INFRA_RC = 75
MISSING_OLEAN = re.compile(r"object file \S+ of module ([A-Za-z_][\w'.]*) does not exist")
INFRA_MARK = "INFRASTRUCTURE RETRY (stale live olean)"


def stale_live_clash(out):
    stale = []
    for mod in sorted(set(STALE_CLASH.findall(out))):
        mod = mod.rstrip(".")
        if mod in CURRENT: continue
        rel = mod.replace(".", "/")
        try:
            if (lc.P / (rel + ".lean")).stat().st_mtime > (lc.BUILD / (rel + ".olean")).stat().st_mtime: stale.append(mod)
        except OSError:
            pass
    # a live module with a source but no published olean yet (merged upstream, the live build not yet published)
    for mod in sorted(set(MISSING_OLEAN.findall(out))):
        rel = mod.replace(".", "/")
        if mod not in CURRENT and mod not in stale and (lc.P / (rel + ".lean")).is_file() and not (lc.BUILD / (rel + ".olean")).exists():
            stale.append(mod)
    return stale


def published():
    try: return PUBLISHED.stat().st_mtime_ns
    except OSError: return None


def run_files(files, progress=None):
    """(rc, out); a failure that met a publication of the live build (files replaced under Lean) is tried once more."""
    for attempt in (0, 1):
        before = published()
        try:
            return run(files, progress)
        except CompileError as exc:
            rc, out = exc.rc, exc.out
        except (OSError, ValueError, RuntimeError) as exc:
            rc, out = 2, repr(exc) if isinstance(exc, OSError) else str(exc)
        stale = stale_live_clash(out) if rc else []
        if stale:
            FAILED_IN_DELIVERED[0] = False
            return INFRA_RC, (INFRA_MARK + ": the published live build predates (or lacks) the live module " + ", ".join(stale)
                              + "; not the delivery's fault, retry after the next published live build.\n" + out)
        if attempt or (published() == before and "FileNotFoundError" not in out and "No such file" not in out):
            return rc, out
        time.sleep(5)


def compile_plan(plan):
    try:
        files = {m["file"][5:]: m["text"] for m in plan["modules"]}
        if not files: return {"id": plan["id"], "rc": 0, "out": "No new module; existing declarations checked by delivery reader."}
        rc, out = run_files(files)
        return {"id": plan["id"], "rc": rc, "out": out, **({"infra": True} if rc == INFRA_RC else {})}
    except Exception as exc:
        return {"id": plan["id"], "rc": 2, "out": repr(exc)}


def confirm(files, rc, out):
    """scompile.py's rule: a failure is decided by the 60-second server compiler tools/nt_compile.py."""
    local_out = f"LOCAL COMPILE (exit {rc})\n{out}"
    try:
        p = subprocess.run([sys.executable, str(TOOLS / "nt_compile.py"), "--json"], input=json.dumps({"files": files}),
                           capture_output=True, text=True, cwd=ROOT, timeout=60 * (len(files) + 30) + 30)
        server_rc, server_out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as exc:
        def decoded(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        server_rc, server_out = 124, (decoded(exc.stdout) + decoded(exc.stderr) +
                                      "\nServer connection timed out; each Lean invocation still has a 60 s limit.")
    if server_rc:
        server_out = local_out + "\nSERVER CONFIRMATION\n" + server_out
    return server_rc, server_out


def watch_caller():
    """2026-10-18 (waste): a remote caller that went away (ssh closed: the launcher's scompile.py timed out or its worker
    ended) left its call compiling for up to an hour. When the result pipe to the ssh session breaks (POLLERR: no reader
    left), stop the Lean children and exit. Calls not started directly by sshd are never watched."""
    import select, signal, threading
    # only a remote caller: the parent is the ssh session (a local caller, e.g. an agent's check, may close a pipe it
    # does not read and is never watched), and only the result pipe (stdout) counts
    try:
        parent = pathlib.Path(f"/proc/{os.getppid()}/comm").read_text().strip()
    except OSError:
        return
    if not parent.startswith("sshd") or "SSH_CONNECTION" not in os.environ:
        return
    fds = [fd for fd in (1,) if not os.isatty(fd)]
    try:
        import stat as st
        fds = [fd for fd in fds if st.S_ISFIFO(os.fstat(fd).st_mode) or st.S_ISSOCK(os.fstat(fd).st_mode)]
    except OSError:
        return
    if not fds: return
    poller = select.poll()
    for fd in fds: poller.register(fd, select.POLLERR)

    def descendants(pid):
        kids = {}
        for p in pathlib.Path("/proc").iterdir():
            if p.name.isdigit():
                try: kids.setdefault(int((p / "stat").read_text().rsplit(")", 1)[1].split()[1]), []).append(int(p.name))
                except (OSError, ValueError, IndexError): pass
        out, todo = [], [pid]
        while todo:
            for c in kids.get(todo.pop(), []): out.append(c); todo.append(c)
        return out

    def loop():
        while True:
            if any(ev & select.POLLERR for _, ev in poller.poll(5000)):
                try:
                    with open("/dev/shm/nt-tmp/callergone.log", "a") as lf:
                        lf.write(json.dumps({"t": time.strftime("%F %T"), "pid": os.getpid(),
                                             "age": round(time.time() - CALL_START[0])}) + "\n")
                except OSError:
                    pass
                for c in descendants(os.getpid()):
                    try: os.kill(c, signal.SIGKILL)
                    except OSError: pass
                os._exit(141)
    threading.Thread(target=loop, daemon=True).start()


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ("", "--wire", "--wire-confirm", "--warm", "--seed"): raise SystemExit(__doc__)
    pathlib.Path("/dev/shm/nt-tmp").mkdir(exist_ok=True)
    if mode in ("--wire", "--wire-confirm"): watch_caller()
    if mode == "--seed":
        raise SystemExit(seed())
    if mode == "--warm":
        rc, out = run({}, warm=True); print(out[-2000:]); raise SystemExit(rc)
    value = json.load(sys.stdin)
    if "modules" in value:
        print(json.dumps(compile_plan(value))); raise SystemExit(0)
    files = value["files"]
    for rel in files:
        p = pathlib.PurePosixPath(rel)
        if p.is_absolute() or ".." in p.parts or p.suffix != ".lean": raise SystemExit("Invalid relative Lean path: " + rel)
    progress = (lambda m: print(m, file=sys.stderr, flush=True)) if mode else None
    rc, out = run_files(files, progress)
    # 2026-10-17 (cpu): the confirmation recompiles every side import from scratch (minutes of Lean per failed call,
    # 10+ at a time). Lean errors, in the delivered files or in this call's overlay snapshot, against the same live
    # build are final; only timeouts and infrastructure errors (missing object files, exceptions) are confirmed.
    if rc and rc != INFRA_RC and mode == "--wire-confirm" and not FAILED_IN_DELIVERED[0]:
        print(f"LOCAL COMPILE (exit {rc})\n{out}", file=sys.stderr, flush=True)
        print("Confirming against current server sources (60 s per file).", file=sys.stderr, flush=True)
        try:   # 2026-10-17 (cpu): which failures still reach the confirmation
            with open("/dev/shm/nt-tmp/confirm.log", "a") as lf:
                lf.write(json.dumps({"t": time.strftime("%T"), "rc": rc, "files": sorted(files), "head": out[:300], "tail": out[-300:]}) + "\n")
        except OSError:
            pass
        rc, out = confirm(files, rc, out)
    if mode:
        print(json.dumps({"rc": rc, "out": out}))
    else:
        print(out)
    raise SystemExit(rc)
