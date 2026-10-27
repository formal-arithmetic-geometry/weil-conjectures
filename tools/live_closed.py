"""Modules of the live project whose proofs are written (no sorry in the module) (the human, 2026-10-16: stage 2 is
pruned below what stage 3 has finished; a node, stated or not, is not an item once every route to it passes a node whose
Lean is closed). A node whose recorded Lean module is closed in live counts as finished in tools/dag_queue.py.

Source-only: a module counts as closed when its own text has no `sorry`/`admit` outside comments. That is enough for
stage 2: its proofs are written and compile, so everything they use is already stated; unstated nodes below it are not
used by them. Sorries further down are stage-3 items of the live project, not stage-2 work. Cached in local/stage2/live-closed.json by the live HEAD commit."""
import json, os, pathlib, re, subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIVE = pathlib.Path(os.environ.get("SHEAF_LIVE_REPO", "/home/ubuntu/weil-conjectures-sheaf"))
CACHE = pathlib.Path(os.environ.get("SHEAF_LIVE_CLOSED_CACHE") or ROOT / "local" / "stage2" / "live-closed.json")   # keyed by live HEAD; shared by preflight slots
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
HOLE = re.compile(r"\b(sorry|admit)\b")
_closed = None


def _strip(t):
    return re.sub(r"--[^\n]*|/-.*?-/", "", t, flags=re.S)


def _scan(p, memo, used):
    """(the imports, whether a hole remains) of the text of p, as _compute reads it. 2026-10-24 (cpu): memoized on the
    file's identity and stat (inode, size, mtime, ctime), across runs in FILES; a changed file is read again."""
    try:
        st = os.stat(p)
        key = (str(p), st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    except OSError:
        key = None
    hit = memo.get(key) if key else None
    if hit is None:
        t = _strip(p.read_text(errors="ignore"))
        hit = (IMPORT.findall(t), bool(HOLE.search(t)))
        if key:
            memo[key] = hit
    if key:
        used[key] = hit
    return hit


def _compute():
    src = LIVE / "lean"
    files = {}
    for p in src.rglob("*.lean"):
        if ".lake" in p.parts or ".sandbox" in p.parts:
            continue
        files[".".join(p.relative_to(src).with_suffix("").parts)] = p
    memo, used = _load_files_memo(), {}
    state = {}                                   # module -> True (closed) / False
    # 2026-10-24: modules being visited. An import cycle in live (a landing or a sync can bring one in for a while)
    # made this walk expand the cycle forever: check_dag.py grew to 67 GB in an hour and stalled the server. A module
    # met again while it is being visited is on a cycle: it counts as not closed (it cannot compile as it stands).
    visiting = set()
    for root in files:
        if root in state:
            continue
        stack = [(root, False)]
        while stack:
            m, done = stack.pop()
            if m in state:
                continue
            raw, hole = _scan(files[m], memo, used)
            deps = [i for i in raw if i in files]
            if not done:
                if m in visiting:
                    state[m] = False
                    continue
                visiting.add(m)
                stack.append((m, True))
                stack.extend((i, False) for i in deps if i not in state)
                continue
            visiting.discard(m)
            state[m] = not hole and all(state.get(i, True) for i in deps)
    _save_files_memo(used)
    return sorted(m for m, ok in state.items() if ok)


FILES = CACHE.with_name(CACHE.name + ".files.pickle")   # the per-file memo of _scan (only entries of the last scan kept)


def _load_files_memo():
    import pickle
    try:
        with open(FILES, "rb") as f:
            d = pickle.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _save_files_memo(d):
    import pickle
    try:
        FILES.parent.mkdir(parents=True, exist_ok=True)
        tmp = FILES.with_name(FILES.name + f".{os.getpid()}.tmp")
        with open(tmp, "wb") as f:
            pickle.dump(d, f, protocol=pickle.HIGHEST_PROTOCOL)
        os.replace(tmp, FILES)
    except Exception:
        pass


def closed():
    global _closed
    if _closed is not None:
        return _closed
    try:
        # fastland 2026-10-17: keyed by the lean/ tree, the input of _compute (live HEAD moved with every DAG commit)
        head = subprocess.run(["git", "-C", str(LIVE), "rev-parse", "HEAD:lean"], capture_output=True, text=True).stdout.strip()
        head = ("lean-tree:" + head) if head else ""
    except Exception:
        head = ""
    def cached():
        try:
            c = json.loads(CACHE.read_text())
            if head and c.get("head") == head:
                return set(c["modules"])
        except Exception:
            pass
        return None
    _closed = cached()
    if _closed is not None:
        return _closed
    # 2026-10-24 (cpu): one computation per key; the other processes wait for it and read it (every preflight running
    # when the lean tree moved used to recompute it, ~15 s of CPU each), and the file is replaced atomically (a reader
    # could see it half written and recompute)
    lk = None
    if head:
        try:
            import fcntl
            CACHE.parent.mkdir(parents=True, exist_ok=True)
            lk = open(CACHE.with_name(CACHE.name + ".lock"), "a")
            fcntl.flock(lk, fcntl.LOCK_EX)
            _closed = cached()
            if _closed is not None:
                lk.close()
                return _closed
        except OSError:
            pass
    try:
        mods = _compute() if LIVE.is_dir() else []
        try:
            CACHE.parent.mkdir(parents=True, exist_ok=True)
            tmp = CACHE.with_name(CACHE.name + f".{os.getpid()}.tmp")
            tmp.write_text(json.dumps({"head": head, "modules": mods}))
            os.replace(tmp, CACHE)
        except Exception:
            pass
    finally:
        if lk:
            lk.close()
    _closed = set(mods)
    return _closed


_axioms = None


def axioms_ok():
    """tools/live_axioms.py: declaration -> its axioms exclude sorryAx (for modules whose closure has an unused sorry)."""
    global _axioms
    if _axioms is None:
        try: _axioms = json.loads((ROOT / "local" / "stage2" / "live-axioms.json").read_text()).get("ok", {})
        except Exception: _axioms = {}
    return _axioms


def node_closed(d) -> bool:
    rec = d.get("lean") if isinstance(d, dict) else None
    if not isinstance(rec, dict) or not rec.get("module"): return False
    if rec["module"] in closed(): return True
    names = ([rec["declaration"]] if rec.get("declaration") else []) + [x for x in rec.get("declarations") or [] if isinstance(x, str)]
    ok = axioms_ok()
    return bool(names) and all(ok.get(x) is True for x in names)
