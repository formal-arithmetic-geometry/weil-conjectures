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


def _compute():
    src = LIVE / "lean"
    files = {}
    for p in src.rglob("*.lean"):
        if ".lake" in p.parts or ".sandbox" in p.parts:
            continue
        files[".".join(p.relative_to(src).with_suffix("").parts)] = p
    state = {}                                   # module -> True (closed) / False
    for root in files:
        if root in state:
            continue
        stack = [(root, False)]
        while stack:
            m, done = stack.pop()
            if m in state:
                continue
            t = _strip(files[m].read_text(errors="ignore"))
            deps = [i for i in IMPORT.findall(t) if i in files]
            if not done:
                stack.append((m, True))
                stack.extend((i, False) for i in deps if i not in state)
                continue
            state[m] = not HOLE.search(t) and all(state.get(i, True) for i in deps)
    return sorted(m for m, ok in state.items() if ok)


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
    try:
        c = json.loads(CACHE.read_text())
        if head and c.get("head") == head:
            _closed = set(c["modules"]); return _closed
    except Exception:
        pass
    mods = _compute() if LIVE.is_dir() else []
    try:
        CACHE.parent.mkdir(parents=True, exist_ok=True)
        CACHE.write_text(json.dumps({"head": head, "modules": mods}))
    except Exception:
        pass
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
