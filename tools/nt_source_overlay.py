"""Which library modules a stage-1/2 compile builds privately instead of reading the published build.

Retirement of ~/weil-newtargets (2026-10-19, the human: one library; workers compile single files against the last green
build of that library plus their own sandbox files): there is no side tree and no override manifest any more. A module
of this repository is compiled privately (content-addressed, cached by the callers) only when the published build has
no usable artifact for it:
  * its .olean is missing from lean/.lake/build (landed after the last green build, or never built), or
  * its source was committed after the published build and was absent from that build's commit: an existing
    artifact at that path is a leftover, not evidence that the new module was published, or
  * it is a module of the source library (WeilConjectures/, Comparator/) that the lake targets do not reach: the
    published artifact of such a module is a stale leftover (lake never rebuilds it), e.g. the compatibility re-exports
    of the 2026-10-17 upstream sync whose old full .olean would duplicate the FiniteCoefficient declarations.
  * a committed legacy-to-module header conversion has identical declaration text
    to the last published source (module workers cannot load the legacy artifact).
Everything else is read from the published build, as the stage-3 compile (lcompile) does: the last green build is the
library a worker compiles against.

The unreachable set is computed once per published build (local/builds/published stamp) and cached in
/dev/shm/nt-tmp/unbuilt-<stamp>.json; the missing set is checked per import with one stat.
Committed additions are compared once per published commit and HEAD; working-source Git blob hashes
are rechecked before selecting them. Neither old cache links nor artifact mtimes establish publication.
"""
import hashlib
import json
import os
import pathlib
import re
import subprocess

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
CACHE_DIR = pathlib.Path("/dev/shm/nt-tmp")
SOURCE_LIBS = ("WeilConjectures", "Comparator")
_UNBUILT = {}
_HEADER_CONVERSIONS = {}
_COMMITTED_ADDITIONS = {}


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


def committed_additions(live, rel=None):
    """Exact committed sources absent from the last published build, even if an old artifact exists.

    Do not select modified published modules or uncommitted edits. Both compile paths must use the
    same rule; cache Git's comparison by the publication and HEAD, then recheck working file content.
    """
    lean = _lean(live)
    root = lean.parent
    try:
        published = json.loads((root / "local/builds/published.json").read_text())["commit"]
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True, stderr=subprocess.PIPE).strip()
        cache_key = (str(lean), published, head)
        if cache_key not in _COMMITTED_ADDITIONS:
            changed = subprocess.check_output(
                ["git", "diff", "--raw", "--no-abbrev", "--no-renames", "-z",
                 "--diff-filter=A", published, head, "--", "lean/Sheaf",
                 "lean/WeilConjectures", "lean/Comparator"],
                cwd=root, stderr=subprocess.PIPE).decode().split("\0")
            blobs = {}
            for record, path in zip(changed[::2], changed[1::2]):
                if path.endswith(".lean"):
                    added_rel = pathlib.Path(path).relative_to("lean").as_posix()
                    blobs[added_rel] = record.split()[3]
            _COMMITTED_ADDITIONS.clear()
            _COMMITTED_ADDITIONS[cache_key] = blobs
        blobs = _COMMITTED_ADDITIONS[cache_key]
        if rel is not None:
            blobs = {rel: blobs[rel]} if rel in blobs else {}
        out = set()
        for rel, blob in blobs.items():
            try:
                body = (lean / rel).read_bytes()
            except OSError:
                continue
            digest = hashlib.new("sha256" if len(blob) == 64 else "sha1")
            digest.update(f"blob {len(body)}\0".encode())
            digest.update(body)
            if digest.hexdigest() == blob:
                out.add(rel)
        return frozenset(out)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError):
        return frozenset()


_COMMITTED_MODIFICATIONS = {}


def _red_failing(root):
    """Sources (relative to lean/) of the modules the latest global build failed on, when it was red."""
    try:
        last = json.loads((root / "local/builds/last.json").read_text())
        if last.get("result") == "red":
            return {m.replace(".", "/") + ".lean" for m in last.get("failing") or []}
    except (OSError, ValueError, AttributeError):
        pass
    return set()


def committed_modifications(live, rel=None):
    """2026-10-25 (deliverfix; the human: a stale publication is a tool bug, use the current one): exact committed
    sources MODIFIED since the last green publication. Their published artifacts are stale (e.g. a structure made
    two-universe on HEAD while the published .olean keeps one universe: every delivery using the new signature was
    refused while the global build stayed red). They are compiled privately from the committed text, as additions are;
    a module the latest red build failed on keeps its published artifact (its current source does not compile).
    Uncommitted edits are never selected (working file must equal the committed blob)."""
    lean = _lean(live)
    root = lean.parent
    try:
        published = json.loads((root / "local/builds/published.json").read_text())["commit"]
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True, stderr=subprocess.PIPE).strip()
        cache_key = (str(lean), published, head)
        if cache_key not in _COMMITTED_MODIFICATIONS:
            changed = subprocess.check_output(
                ["git", "diff", "--raw", "--no-abbrev", "--no-renames", "-z",
                 "--diff-filter=M", published, head, "--", "lean/Sheaf",
                 "lean/WeilConjectures", "lean/Comparator"],
                cwd=root, stderr=subprocess.PIPE).decode().split("\0")
            blobs = {}
            for record, path in zip(changed[::2], changed[1::2]):
                if path.endswith(".lean"):
                    blobs[pathlib.Path(path).relative_to("lean").as_posix()] = record.split()[3]
            _COMMITTED_MODIFICATIONS.clear()
            _COMMITTED_MODIFICATIONS[cache_key] = blobs
        blobs = _COMMITTED_MODIFICATIONS[cache_key]
        if rel is not None:
            blobs = {rel: blobs[rel]} if rel in blobs else {}
        failing = _red_failing(root)
        out = set()
        for r, blob in blobs.items():
            if r in failing:
                continue
            try:
                body = (lean / r).read_bytes()
            except OSError:
                continue
            digest = hashlib.new("sha256" if len(blob) == 64 else "sha1")
            digest.update(f"blob {len(body)}\0".encode())
            digest.update(body)
            if digest.hexdigest() == blob:
                out.add(r)
        return frozenset(out)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError):
        return frozenset()


def _header_conversion(before, after):
    """Accept only a legacy-to-module conversion with identical declaration text."""
    module = re.compile(r"^module[ \t]*$", re.M)
    exposed = re.compile(r"^@\[expose\] public section[ \t]*$", re.M)
    if module.search(before) or not module.search(after) or not exposed.search(after):
        return False

    def body(text):
        text = re.sub(r"^module[ \t]*\n\n?", "", text, count=1, flags=re.M)
        text = re.sub(r"^@\[expose\] public section[ \t]*\n\n?", "", text,
                      count=1, flags=re.M)
        text = re.sub(r"^public import ", "import ", text, flags=re.M)
        return text

    return body(before) == body(after)


def module_header_conversions(live):
    """Committed header-only migrations not yet present in the published build.

    These preserve every declaration, but the legacy artifact cannot be imported
    by a module-mode worker. Compile the exact committed sources privately until
    the next green publication. Mathematical changes remain on published artifacts.
    """
    lean = _lean(live)
    root = lean.parent
    try:
        published = json.loads((root / "local/builds/published.json").read_text())["commit"]
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True, stderr=subprocess.PIPE).strip()
        cache_key = (str(lean), published, head)
        if cache_key in _HEADER_CONVERSIONS:
            return frozenset(rel for rel, text in _HEADER_CONVERSIONS[cache_key].items()
                             if (lean / rel).is_file() and (lean / rel).read_text() == text)
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", "--diff-filter=M", published, head,
             "--", "lean/Sheaf"], cwd=root, text=True, stderr=subprocess.PIPE).splitlines()
        out = {}
        for path in changed:
            if not path.endswith(".lean"):
                continue
            committed = subprocess.check_output(
                ["git", "show", head + ":" + path], cwd=root,
                text=True, stderr=subprocess.PIPE)
            if not re.search(r"^module[ \t]*$", committed, re.M):
                continue
            before = subprocess.check_output(
                ["git", "show", published + ":" + path], cwd=root,
                text=True, stderr=subprocess.PIPE)
            if not _header_conversion(before, committed):
                continue
            out[pathlib.Path(path).relative_to("lean").as_posix()] = committed
        _HEADER_CONVERSIONS.clear()
        _HEADER_CONVERSIONS[cache_key] = out
        return frozenset(rel for rel, text in out.items()
                         if (lean / rel).is_file() and (lean / rel).read_text() == text)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError):
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
    if committed_additions(lean, rel):
        return src
    if committed_modifications(lean, rel):
        return src
    if rel in module_header_conversions(lean):
        return src
    if rel.split("/")[0] in SOURCE_LIBS and rel in unbuilt(live):
        return src
    return None


def overlay_sources(root, live):
    """Every module compiled privately by the rule above, {rel: bytes}."""
    lean = _lean(live)
    pub = lean / ".lake/build/lib/lean"
    out = {}
    for rel in unbuilt(live) | module_header_conversions(lean) | committed_additions(lean) | committed_modifications(lean):
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
