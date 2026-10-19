"""Which library modules a stage-1/2 compile builds privately instead of reading the published build.

Retirement of ~/weil-newtargets (2026-10-19, the human: one library; workers compile single files against the last green
build of that library plus their own sandbox files): there is no side tree and no override manifest any more. A module
of this repository is compiled privately (content-addressed, cached by the callers) only when the published build has
no usable artifact for it:
  * its .olean is missing from lean/.lake/build (landed after the last green build, or never built), or
  * it is a module of the source library (WeilConjectures/, Comparator/) that the lake targets do not reach: the
    published artifact of such a module is a stale leftover (lake never rebuilds it), e.g. the compatibility re-exports
    of the 2026-10-17 upstream sync whose old full .olean would duplicate the FiniteCoefficient declarations.
Everything else is read from the published build, as the stage-3 compile (lcompile) does: the last green build is the
library a worker compiles against.

The unreachable set is computed once per published build (local/builds/published stamp) and cached in
/dev/shm/nt-tmp/unbuilt-<stamp>.json; the missing set is checked per import with one stat.
"""
import json
import os
import pathlib
import re

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
CACHE_DIR = pathlib.Path("/dev/shm/nt-tmp")
SOURCE_LIBS = ("WeilConjectures", "Comparator")
_UNBUILT = {}


def _lean(live):
    live = pathlib.Path(live)
    return live if (live / "lakefile.toml").is_file() else live / "lean"


def _roots(lean):
    """Root modules of the lake targets of lean/lakefile.toml that are not globs (globs, e.g. Sheaf.+, build every module)."""
    import tomllib
    cfg = tomllib.loads((lean / "lakefile.toml").read_text())
    roots = []
    for lib in cfg.get("lean_lib", []):
        if lib.get("globs"):
            continue
        src = lib.get("srcDir", ".")
        for r in lib.get("roots") or [lib["name"]]:
            roots.append((src, r))
    return roots


def unbuilt(live):
    """Source-library modules the lake targets do not reach (their published artifacts are stale), as relative paths."""
    lean = _lean(live)
    stamp_file = lean.parent / "local/builds/published"
    try:
        stamp = str(stamp_file.stat().st_mtime_ns)
    except OSError:
        stamp = "none"
    if _UNBUILT.get("stamp") == stamp:
        return _UNBUILT["set"]
    cache = CACHE_DIR / f"unbuilt-{stamp}.json"
    try:
        out = frozenset(json.loads(cache.read_text()))
        _UNBUILT.update(stamp=stamp, set=out)
        return out
    except (OSError, ValueError):
        pass
    seen, stack = set(), []
    for src, r in _roots(lean):
        rel = (pathlib.PurePosixPath(src) / (r.replace(".", "/") + ".lean")).as_posix().lstrip("./")
        stack.append(rel)
    def path_of(mod):
        for base in ("", "Comparator/"):
            rel = base + mod.replace(".", "/") + ".lean"
            if (lean / rel).is_file():
                return rel
        return None
    while stack:
        rel = stack.pop()
        if rel in seen:
            continue
        seen.add(rel)
        try:
            text = (lean / rel).read_text(errors="ignore")
        except OSError:
            continue
        for m in IMPORT.findall(text):
            if m.split(".")[0] in ("Mathlib", "Batteries", "Qq", "Aesop", "Lean", "Init", "Std", "Proetale", "Plausible", "ImportGraph", "LeanSearchClient", "Cli", "ProofWidgets"):
                continue
            p = path_of(m)
            if p and p not in seen:
                stack.append(p)
    out = set()
    for lib in SOURCE_LIBS:
        for p in (lean / lib).rglob("*.lean"):
            rel = p.relative_to(lean).as_posix()
            if rel not in seen:
                out.add(rel)
    out = frozenset(out)
    try:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        tmp = cache.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(sorted(out)))
        os.replace(tmp, cache)
    except OSError:
        pass
    _UNBUILT.update(stamp=stamp, set=out)
    return out


def load_overrides(root):
    """No override manifest any more (one library); kept for the callers' interface."""
    return frozenset()


def source_for_import(root, live, rel, overrides=frozenset()):
    """The source file to compile privately for the import `rel` (path under lean/), or None to use the published build."""
    rel = pathlib.PurePosixPath(rel).as_posix()
    lean = _lean(live)
    src = lean / rel
    if not src.is_file():
        return None
    published = lean / ".lake/build/lib/lean" / pathlib.PurePosixPath(rel).with_suffix(".olean")
    if not published.is_file():
        return src
    if rel.split("/")[0] in SOURCE_LIBS and rel in unbuilt(live):
        return src
    return None


def overlay_sources(root, live):
    """Every module compiled privately by the rule above, {rel: bytes}: missing artifacts and unbuilt source modules."""
    lean = _lean(live)
    pub = lean / ".lake/build/lib/lean"
    out = {}
    for rel in unbuilt(live):
        try:
            out[rel] = (lean / rel).read_bytes()
        except OSError:
            pass
    for name in ("Sheaf", "WeilConjectures"):
        for p in (lean / name).rglob("*.lean"):
            rel = p.relative_to(lean).as_posix()
            if rel not in out and not (pub / pathlib.PurePosixPath(rel).with_suffix(".olean")).is_file():
                out[rel] = p.read_bytes()
    return out
