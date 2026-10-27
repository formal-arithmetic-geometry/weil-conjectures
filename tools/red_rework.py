#!/usr/bin/env python3
"""A failing module that no landing of the red build wrote becomes a rework item (the human, 2026-10-24: "哪个文件报错了
就汇报给编辑过这个的worker，如果没有就单独把文件的这个报错作为一个新的返工任务"; no attribution, no guessing).

quarantine(failing, causes, note) moves each failing module and its importers (transitively) to quarantine/ and writes
their rows in coord/rework.tsv, exactly as the upstream sync's red rounds do (~/cc1/upsync-quick.py quarantine): the
root files that only list imports lose their lines (put back on restore), the failing ones are marked tried so the
cluster restore does not put them straight back, one commit and one landing record (group L) under coord/.merge.lock
and local/tree.lock. `causes` {module: text} is the build's error of the module, with the build's landings that
changed modules it imports (for the worker; nothing is taken out for it). Returns (landing id, moved modules), or
raises Refuse when a module of the six target statements' closure would move (the caller keeps its old handling).

    python3 tools/red_rework.py <module>...      (manual use: quarantine these failing modules with their build error)
    python3 tools/red_rework.py --dangling [--dry-run]   (move every library module importing a module gone from lean/)

take_out_importers(note) (2026-10-26) is the same move for the modules whose imports reach a module already gone from
lean/; batch_recovery.commit_inverse and rework._drop_mine call it inside their take-out commit.
"""
from __future__ import annotations
import fcntl, hashlib, json, os, re, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanindex as li  # noqa: E402
import landing as ld  # noqa: E402
import mergelock  # noqa: E402
import rework  # noqa: E402

ROOT = li.ROOT
IDENT = ["-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "-c", "commit.template="]
TRAILER = "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"


class Refuse(Exception):
    pass


def git(*a, check=True):
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(a[:3])}: {(r.stderr or r.stdout)[-300:]}")
    return r.stdout


def first_errors(failing) -> dict[str, str]:
    """module -> its error block in the build log (up to 12 lines)"""
    out = {}
    try:
        text = (ld.LOCAL / "build.log").read_text(errors="ignore")
    except OSError:
        return out
    lines = text.splitlines()
    for m in failing:
        p = m.replace(".", "/") + ".lean"
        hit = [k for k, l in enumerate(lines) if p in l and "error" in l]
        if hit:
            out[m] = " | ".join(re.sub(r"\s+", " ", l.strip())[:300] for l in lines[hit[0]:hit[0] + 12] if l.strip())[:1500]
    return out


def add_suggested_imports(failing, messages) -> tuple[str, list[str]]:
    """2026-10-24: a module that fails only because a declaration is "imported privately; consider adding `public import
    X`" gets that import (the compiler names the fix; an upstream module stopped re-exporting X). One commit and one
    landing record (group L). Returns (landing id, fixed modules)."""
    want = {}
    for m in failing:
        xs = sorted(set(re.findall(r"consider adding `public import ([\w.']+)`", messages.get(m) or "")))
        f = li.file_of(m)
        if xs and f.is_file():
            want[m] = (f, xs)
    if not want:
        return "", []
    lf = open(mergelock.LOCK, "a"); mergelock.acquire(lf, mergelock.LOCK, 3600)
    try:
        with ld.tree_lock():
            prev, paths = {}, []
            for m, (f, xs) in want.items():
                t = f.read_text(); lines = t.split("\n")
                k = max((i for i, l in enumerate(lines) if l.startswith(("import ", "public import "))), default=0)
                new = [f"public import {x}" for x in xs if f"public import {x}" not in t]
                if not new:
                    continue
                prev[str(f.relative_to(li.LEAN))] = t.encode()
                lines[k + 1:k + 1] = new; f.write_text("\n".join(lines)); paths.append(str(f.relative_to(ROOT)))
            if not paths:
                return "", []
            git("add", "--", *paths)
            git(*IDENT, "commit", "-q", "-m", f"red build: add the public imports the compiler named in {len(paths)} module(s)"
                + TRAILER, "--", *paths)
            rid = ld.new_record("L", prev, "red build: add the public imports the compiler named", kind="interface")["id"]
            return rid, [m for m in want if str(want[m][0].relative_to(ROOT)) in paths]
    finally:
        fcntl.flock(lf, fcntl.LOCK_UN); lf.close()


def _comparator_file(m: str):
    return (li.LEAN / "Comparator").joinpath(*m.split(".")).with_suffix(".lean")


def live_imports() -> dict[str, set[str]]:
    """module -> its imports, read now from every library file (li.scan's cache can predate a take-out in progress)"""
    out = {}
    for p in li.library_files():
        try:
            out[li.module_of(p)] = li.imports_of(p.read_text(errors="ignore"))
        except OSError:
            pass
    return out


def dangling(imports: dict | None = None) -> dict[str, set[str]]:
    """library module -> its project imports that are in no library file (back in quarantine/, or nowhere)"""
    imports = live_imports() if imports is None else imports
    out = {}
    for m, ims in imports.items():
        miss = {i for i in ims if i.startswith(rework.PROJECT_PREFIXES) and i not in imports
                and not li.file_of(i).is_file() and not _comparator_file(i).is_file()}
        if miss:
            out[m] = miss
    return out


def _plan(roots: set[str], imports: dict) -> tuple[set[str], dict]:
    """(the library modules that leave with `roots`, the blocked target libraries {lib: modules}). `roots` are failing
    library modules or modules already gone from lean/ (their importers leave, they themselves are not moved)."""
    closure = rework.importer_closure(roots, imports)
    # 2026-10-25: li.scan() does not read lean/Comparator/, so "Weil.Solution" was never in the closure and
    # 9bca5457fbb moved WeilConjectures.Statement, which the lakefile root Weil.Solution imports: every later build
    # failed with "bad import". The project modules the comparator files import are kept like the target statements.
    kept = set(rework.ROOTS_KEPT)
    for f in (li.LEAN / "Comparator").rglob("*.lean"):
        kept |= li.imports_of(f.read_text(errors="ignore"))
    hit = sorted(closure & kept)
    # 2026-10-26 (the human: "为什么涉及目标就不能暂时阻塞？…派单给优先修复队列，期待在两次构建内解决"): a failure that
    # reaches the target statements is quarantined like any other; the locked statement files (ROOTS_KEPT) stay where
    # they are, and the libraries whose roots import a moved module are blocked: tools/build.py leaves them out of the
    # global build (local/builds/blocked-targets.json) until the rework restores the modules. The rework item is the
    # dispatcher's first lane. No size cap either (the 100-module cap of 2026-10-24 is lifted by the same decision).
    blocked_roots = {}
    if hit or "Weil.Solution" in closure:
        if os.environ.get("SHEAF_RED_BLOCK_TARGETS", "1") != "1":
            raise Refuse(f"the failures reach {', '.join(hit or ['Weil.Solution'])}")
        closure -= set(rework.ROOTS_KEPT)
        lib_roots = {"Solution": (li.LEAN / "Comparator" / "Weil" / "Solution.lean"),
                     "SheafChallenge": (li.LEAN / "Challenge.lean")}
        for lib, rf in lib_roots.items():
            if not rf.is_file():
                continue
            need = set()
            for i in li.imports_of(rf.read_text(errors="ignore")):
                need |= {i} | li.closure(i, imports, {})
            if need & closure:
                blocked_roots[lib] = sorted(need & closure)
    for r in rework.IMPORT_ROOTS:
        closure.discard(r)
    closure = {m for m in closure if m in imports}      # a gone root is not moved (it is not in lean/)
    if len(closure) > int(os.environ.get("SHEAF_RED_MAX_MOVE", "1000000")):
        raise Refuse(f"{len(closure)} modules would leave the library (roots: {', '.join(sorted(roots)[:6])})")
    return closure, blocked_roots


def _move(closure: set[str], failing: set[str], gone: set[str], causes: dict[str, str], imports: dict,
          blocked_roots: dict, before: dict | None = None) -> tuple[dict, list[str], list[str], dict]:
    """Move `closure` from lean/ to quarantine/ with their coord/rework.tsv rows, drop the import lines of moved and
    gone modules from the IMPORT_ROOTS files, mark the moved texts tried, block the target libraries. The caller holds
    coord/.merge.lock and local/tree.lock and commits. Returns (prev {lean rel: bytes}, moved, repository paths to
    commit, before {repository path: bytes or None} of every committed path, for a rollback)."""
    memo: dict = {}
    nodes = rework.nodes_of(closure)
    stamp = time.strftime("%FT%TZ", time.gmtime())
    before = {} if before is None else before

    def keep(p) -> None:
        rel = str(p.relative_to(ROOT))
        if rel not in before:
            before[rel] = p.read_bytes() if p.is_file() else None

    roots = failing | gone
    rows = rework.load()
    keep(ROOT / "coord" / "rework.tsv")
    prev: dict[str, bytes | None] = {}
    moved = []
    for m in sorted(closure):
        src = li.file_of(m)
        if not src.is_file():
            continue
        rel = str(src.relative_to(li.LEAN))
        dst = ROOT / rework.qpath(m)
        keep(src); keep(dst)
        prev[rel] = src.read_bytes()
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(prev[rel]); src.unlink()
        if m in failing:
            cause = causes.get(m) or "error: failed in the global build (no message located)"
        else:
            cause = "imports " + next(iter(sorted(li.closure(m, imports, memo) & roots)), "?")
        rows[m] = {"module": m, "original": rework.opath(m), "quarantine": rework.qpath(m),
                   "sync": f"build {time.strftime('%F')}", "time": stamp, "cause": cause,
                   "nodes": ",".join(sorted(nodes.get(m, [])))}
        moved.append(m)
    # tried at the published build too: autorestore compiles a quarantined text against the last green build
    # and, with --recheck-errors, again for every new published build. A module a red build quarantined fails
    # because of landings after that green build, so against it the text compiles and went straight back
    # (AdicSmoothDualizingComplexes, 12:49 out, 12:51 back, 12:57 out, 2026-10-24); it is retried only against
    # a newer green build, which contains those landings.
    try:
        tried = json.loads(rework.TRIED.read_text()) if rework.TRIED.exists() else {}
        tb = json.loads(rework.TRIED_BUILD.read_text()) if rework.TRIED_BUILD.exists() else {}
        pub = rework._published()
        for m in moved:
            q = ROOT / rework.qpath(m)
            if q.is_file():
                tried[m] = hashlib.sha1(q.read_bytes()).hexdigest(); tb[m] = pub
        for f, d in ((rework.TRIED, tried), (rework.TRIED_BUILD, tb)):
            tmp = f.with_suffix(".tmp"); tmp.write_text(json.dumps(d)); os.replace(tmp, f)
    except Exception:  # noqa: BLE001
        pass
    for r in rework.IMPORT_ROOTS:
        root = li.LEAN / f"{r}.lean"
        if not root.is_file():
            continue
        rt = root.read_text()
        h = (set(moved) | gone) & li.imports_of(rt)
        if h:
            keep(root)
            prev[f"{r}.lean"] = rt.encode(); root.write_text(rework.drop_import_lines(rt, h))
            for m in h:
                if m in rows:
                    rows[m]["roots"] = ",".join(filter(None, (rows[m].get("roots", "").split(",") + [r])))
    rework.save(rows)
    if blocked_roots:
        bf = ld.B / "blocked-targets.json"
        cur = ld.read_json(bf) or {"libs": {}}
        cur.setdefault("libs", {})
        for lib, mods in blocked_roots.items():
            cur["libs"][lib] = sorted(set(cur["libs"].get(lib, [])) | (set(mods) & (set(moved) | gone)))
        cur["since"] = cur.get("since") or stamp
        cur["failing"] = sorted(set(cur.get("failing", [])) | failing | gone)
        ld.write_json(bf, cur)
    paths = ["lean/" + rel for rel in prev] + [rework.qpath(m) for m in moved] + ["coord/rework.tsv"]
    tracked = set(git("ls-files", "--", *sorted(set(paths))).split("\n"))
    paths = sorted(p for p in set(paths) if (ROOT / p).exists() or p in tracked)
    return prev, moved, paths, before


def _record(prev: dict, note: str) -> str:
    files = {rel: b for rel, b in prev.items()
             if ld.sha(li.LEAN / rel) != (hashlib.sha256(b).hexdigest() if b is not None else None)}
    return ld.new_record("L", files, note, kind="interface")["id"] if files else ""


def quarantine(failing: set[str], causes: dict[str, str], note: str) -> tuple[str, list[str]]:
    _, imports = li.scan()
    lib = set(imports)
    failing = {m for m in failing if m in lib}
    try:   # 2026-10-27: an early item (tools/early_red.py) whose fix landed after the build's snapshot stays in the library
        import early_red
        kept = {m for m in failing if early_red.fixed_since(m)}
        if kept:
            print(f"red_rework: fixed since the build (early item), not quarantined; the next build verifies: {' '.join(sorted(kept))}", flush=True)
            failing -= kept
    except Exception:  # noqa: BLE001
        pass
    if not failing:
        return "", []
    _plan(failing, imports)         # refuses before taking the locks (SHEAF_RED_BLOCK_TARGETS=0, SHEAF_RED_MAX_MOVE)
    lf = open(mergelock.LOCK, "a")
    mergelock.acquire(lf, mergelock.LOCK, 3600)
    try:
        with ld.tree_lock():
            # 2026-10-26: also every library module that imports a module already gone from lean/ (a take-out left it)
            # (the import graph read now, under the locks), and every library module importing a module already
            # gone from lean/ (2026-10-26: a take-out left them; they failed the next build with "bad import")
            imports = live_imports()
            gone = set().union(set(), *dangling(imports).values())
            closure, blocked_roots = _plan(failing | gone, imports)
            prev, moved, paths, _ = _move(closure, failing, gone, causes, imports, blocked_roots)
            for i in range(0, len(paths), 500):
                git("add", "-A", "--", *paths[i:i + 500])
            git(*IDENT, "commit", "-q", "-m",
                f"red build: {len(failing)} failing module(s) no landing wrote and {len(moved) - len(failing & set(moved))} "
                f"importer(s) moved to quarantine/ as rework ({note})" + TRAILER, "--", *paths)
            rid = _record(prev, f"red build rework: {note}")
    finally:
        fcntl.flock(lf, fcntl.LOCK_UN); lf.close()
    return rid, moved


def take_out_importers(note: str) -> tuple[list[str], list[str], dict, dict] | None:
    """2026-10-26: whenever a module leaves lean/ (a take-out deletes a restored or new module, a red build quarantines
    one), every library module whose imports reach it leaves too, in the same commit: left behind they fail the next
    build with "bad import" (20:45 take-out of the cluster restore: WeilConjectures.Statement gone, Solution kept;
    21:05: 11 bad imports). Reads the tree now and takes every library module with a project import that is in no
    library file, with its importers (transitively). The caller holds coord/.merge.lock and local/tree.lock, has
    written its own change, and commits the returned paths with it; then calls `_record(prev, ...)`.
    Returns (paths, moved, prev, before) or None when nothing dangles."""
    imports = live_imports()
    d = dangling(imports)
    if not d:
        return None
    gone = set().union(*d.values())
    closure, blocked_roots = _plan(gone, imports)
    before: dict = {}
    try:
        prev, moved, paths, _ = _move(closure, set(), gone, {}, imports, blocked_roots, before)
    except BaseException:
        for rel, data in before.items():        # a half-done move is undone (the caller's own change is its business)
            p = ROOT / rel
            if data is None:
                p.unlink(missing_ok=True)
            else:
                p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(data)
        raise
    return paths, moved, prev, before


def sweep(note: str, dry: bool = False) -> tuple[str, list[str]]:
    """take_out_importers as its own commit (manual repair, or a caller without a take-out commit)"""
    if dry:
        imports = live_imports()
        d = dangling(imports)
        if not d:
            return "", []
        gone = set().union(*d.values())
        closure, blocked = _plan(gone, imports)
        for m, g in sorted(d.items()):
            print(f"dangling: {m} imports {', '.join(sorted(g))} "
                  f"({'quarantined' if all((ROOT / rework.qpath(x)).is_file() for x in g) else 'not quarantined'})")
        roots_lines = {r: sorted(gone & li.imports_of((li.LEAN / f'{r}.lean').read_text(errors='ignore')))
                       for r in rework.IMPORT_ROOTS if (li.LEAN / f"{r}.lean").is_file()}
        print(f"would move {len(closure)} module(s); root import lines dropped: {roots_lines}; blocked libraries: {blocked}")
        for m in sorted(closure):
            print("  move", m)
        return "", sorted(closure)
    lf = open(mergelock.LOCK, "a")
    mergelock.acquire(lf, mergelock.LOCK, 3600)
    try:
        with ld.tree_lock():
            r = take_out_importers(note)
            if r is None:
                return "", []
            paths, moved, prev, _ = r
            for i in range(0, len(paths), 500):
                git("add", "-A", "--", *paths[i:i + 500])
            git(*IDENT, "commit", "-q", "-m",
                f"red build: {len(moved)} module(s) importing modules gone from lean/ moved to quarantine/ as rework "
                f"({note})" + TRAILER, "--", *paths)
            rid = _record(prev, f"red build rework: {note}")
    finally:
        fcntl.flock(lf, fcntl.LOCK_UN); lf.close()
    return rid, moved


if __name__ == "__main__":
    os.environ.setdefault("SHEAF_LEAD", "L-only")
    if sys.argv[1:2] == ["--dangling"]:
        # python3 tools/red_rework.py --dangling [--dry-run]: move every library module importing a module gone from lean/
        print(sweep("importers of modules gone from lean/ (manual sweep)", dry="--dry-run" in sys.argv))
        sys.exit(0)
    ms = set(sys.argv[1:])
    if not ms:
        print(__doc__); sys.exit(2)
    print(quarantine(ms, first_errors(ms), "manual"))
