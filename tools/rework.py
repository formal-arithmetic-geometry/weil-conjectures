#!/usr/bin/env python3
"""The rework queue: modules the scheduled upstream sync took out of the library (the human, 2026-10-20).

After the sync commit (~/cc1/upsync-quick.py) the global build runs; every module that fails is MOVED out of the
compiled library to quarantine/<its path under lean/> (outside lean/: Lake, the build copy and every tool that reads
lean/ no longer see it), its importers with it, in one commit per round, until the build is green. Each such module is
one row of coord/rework.tsv:

  module <TAB> original path <TAB> quarantine path <TAB> sync <TAB> quarantined (UTC) <TAB> cause <TAB> DAG nodes
         <TAB> roots

`cause` is the build error of the module (`error: ...`) or `imports <module>` for an importer taken out with it.
`roots`: the root files that only list imports (lean/WeilConjectures.lean, the source library's root, and
lean/TargetsCheck.lean, the target check) whose import line of the module was removed; it is put back by the landing
that restores the module. lean/Challenge.lean (the six target statements) is never changed: a failure it imports aborts the sync.

Rules (the human, 2026-10-20):
  1. A rework item has priority over every other queue (all batches, all stages): tools/queue.py lists the open ones
     first (stage 3, kind `rework`), tools/tag_batches.py tags them `rework`, the dispatcher's first lane serves them.
  2. A rework item is OPEN when none of the modules it imports, transitively (its imports read from the quarantined
     copy, the library's from lean/), is itself a rework item: rework proceeds bottom-up, deepest first.
  3. A worker fixes it in its sandbox against the last green build and restores it to its original path (a copy of
     the quarantined file, made to compile; upstream files come back verbatim, the fix goes into our own modules
     unless the module is listed in coord/upstream-statement-exceptions.tsv). It lands through the normal landing and
     merge queue; tools/batch_land.py puts its import lines back into the root files (roots_to_restore) in the same
     landing. When a green build has verified it (the file is at its original path in refs/heads/sheaf-verified and
     the roots there import it), `reconcile` (run by ~/cc1/buildloop.sh after every green build) deletes the
     quarantined copy and the row.
  4. BLOCKING: a normal item whose dependencies include a rework item is not in the queue until that item is fixed:
     stage-1/2 node items whose stmt_deps/proof_deps closure reaches a node realized by a rework module (or which are
     such nodes), and stage-3 module items that import a rework module transitively or realize a blocked node.

Usage:
  tools/rework.py status              the rows, which are open, which wait for deeper rework, and what they block
  tools/rework.py reconcile           drop the rows verified green (refs/heads/sheaf-verified has the original file)
  tools/rework.py autorestore         compile each new root (its quarantined imports are back) as it is; restore those
                                      that compile in one landing, give the others their own error (separate items)
"""
from __future__ import annotations
import collections, datetime, pathlib, re, subprocess, sys, time
import os as _os, sys as _sys
# 2026-10-20: tools/queue.py shadows the stdlib `queue` (the script's directory is sys.path[0]); concurrent.futures
# needs the stdlib one (ThreadPoolExecutor: "module 'queue' has no attribute 'SimpleQueue'"). Import both without
# tools/ on the path; this process never imports tools/queue.py as a module.
_saved = list(_sys.path)
_here = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:] = [p for p in _sys.path if _os.path.abspath(p or ".") != _here]
_sys.modules.pop("queue", None)
import queue as _queue, concurrent.futures  # noqa: E402,F401
_sys.path[:] = _saved

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
FILE = ROOT / "coord" / "rework.tsv"
DONE = ROOT / "coord" / "rework-done.tsv"
QDIR = ROOT / "quarantine"
VERIFIED_REF = "refs/heads/sheaf-verified"
COLS = ("module", "original", "quarantine", "sync", "time", "cause", "nodes", "roots")
HEADER = ("# module\toriginal path\tquarantine path\tsync\tquarantined (UTC)\tcause\tDAG nodes\troots   "
          "(tools/rework.py; written by ~/cc1/upsync-quick.py, rows removed by `tools/rework.py reconcile`)\n")
# never moved out or changed: the six target statements; a failure it imports aborts the sync
ROOTS_KEPT = ("Challenge", "Weil.Challenge", "Weil.Definitions")   # the locked target statements (+ comparator defs)
# root files that only list imports: a quarantined module's import line is removed from them (and put back on restore)
IMPORT_ROOTS = ("WeilConjectures", "TargetsCheck")
SOURCE_ROOT = "WeilConjectures"


def opath(m: str) -> str:
    return "lean/" + m.replace(".", "/") + ".lean"


def qpath(m: str) -> str:
    return "quarantine/" + m.replace(".", "/") + ".lean"


def load() -> dict[str, dict]:
    out = {}
    try:
        lines = FILE.read_text().splitlines()
    except OSError:
        return out
    for l in lines:
        if not l.strip() or l.startswith("#"):
            continue
        r = l.split("\t")
        r += [""] * (len(COLS) - len(r))
        out[r[0]] = dict(zip(COLS, r))
    return out


def save(rows: dict[str, dict]):
    tmp = FILE.with_suffix(".tmp")
    tmp.write_text(HEADER + "".join("\t".join(str(rows[m].get(c, "")).replace("\t", " ").replace("\n", " ")
                                               for c in COLS) + "\n" for m in sorted(rows)))
    tmp.replace(FILE)


def rework_imports(rows: dict[str, dict]) -> dict[str, set[str]]:
    """imports of each rework module, read from its quarantined copy (the original file once a fix landed)"""
    out = {}
    for m, r in rows.items():
        for p in (ROOT / (r.get("quarantine") or qpath(m)), ROOT / opath(m)):
            if p.is_file():
                out[m] = li.imports_of(p.read_text(errors="ignore")); break
        else:
            out[m] = set()
    return out


def landed(m: str) -> bool:
    """a fix has landed: the module is back at its original path (verified or not)"""
    return (ROOT / opath(m)).is_file()


def open_items(rows=None, imports=None) -> list[str]:
    """rework modules that import (transitively) no other rework module and whose fix has not landed yet; deepest first"""
    rows = load() if rows is None else rows
    if not rows:
        return []
    if imports is None:
        _, imports = li.scan()
    rimp = rework_imports(rows)
    graph = dict(imports); graph.update(rimp)
    R = set(rows)
    out, memo = [], {}
    for m in rows:
        if landed(m):
            continue
        if not (li.closure(m, graph, memo) & (R - {m})):
            out.append(m)
    # deepest first: the most rework modules waiting on it (transitive importers among the rework rows)
    rev = collections.defaultdict(set)
    for m in R:
        for i in rimp.get(m, ()):
            if i in R:
                rev[i].add(m)
    def waiting(m):
        seen, st = set(), [m]
        while st:
            for p in rev.get(st.pop(), ()):
                if p not in seen:
                    seen.add(p); st.append(p)
        return len(seen)
    return sorted(out, key=lambda m: (-waiting(m), m))


def clusters(rows=None) -> list[dict]:
    """The rework items as CLUSTERS (the human, 2026-10-20): a root is a quarantined module whose fix has not landed and
    that imports no other open rework module; its cluster is the root and every open rework module that imports it
    (transitively, through rework modules: a library module importing a quarantined one is quarantined itself).
    Clusters sharing members are merged. [{item: the representative root, roots: [...], members: [...] (roots first)}],
    deepest (largest) first. One worker claims the whole cluster through its item."""
    rows = load() if rows is None else rows
    live = {m for m in rows if not landed(m)}
    if not live:
        return []
    rimp = {m: i & live for m, i in rework_imports({m: rows[m] for m in live}).items()}
    roots = sorted(m for m in live if not (rimp.get(m, set()) - {m}))
    rev = collections.defaultdict(set)
    for m, ims in rimp.items():
        for i in ims:
            if i != m:
                rev[i].add(m)
    member_of = {}
    for r in roots:
        seen, st = {r}, [r]
        while st:
            for p in rev.get(st.pop(), ()):
                if p not in seen:
                    seen.add(p); st.append(p)
        member_of[r] = seen
    parent = {r: r for r in roots}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    owner = {}
    for r in roots:
        for m in member_of[r]:
            if m in owner:
                parent[find(r)] = find(owner[m])
            else:
                owner[m] = r
    groups = collections.defaultdict(list)
    for r in roots:
        groups[find(r)].append(r)
    out = []
    for rs in groups.values():
        rs = sorted(rs)
        mem = set().union(*(member_of[r] for r in rs))
        out.append({"item": rs[0], "roots": rs, "members": rs + sorted(mem - set(rs))})
    return sorted(out, key=lambda c: (-len(c["members"]), c["item"]))


RETIRE = ROOT / "coord" / "retire-items.tsv"
# coord/retire-items.tsv (the human, 2026-10-20; hand-off of the twin-retirement agent, coord/changes/
# retire-sheaf-twins-20261020.md "Hand-off"): one Sheaf copy to retire per row, columns item, kind (`retire`), copy, twin,
# class, depth, after (copies to retire first, space-separated), consumers, DAG nodes, API difference. The queue item is
# the copy's module name (kind `retire`, after the rework items, before every other queue). Open when every `after` copy
# is gone from lean/; done when the copy is deleted (verified when refs/heads/sheaf-verified no longer has it).


def retire_rows(open_only: bool = True) -> dict[str, dict]:
    out = {}
    try:
        lines = RETIRE.read_text().splitlines()
    except OSError:
        return out
    for l in lines:
        r = l.split("\t")
        if not l.strip() or l.startswith("#") or len(r) < 4:
            continue
        r += [""] * 10
        copy = r[2]
        after = [x for x in r[6].split() if x and x != "-"]
        if not (ROOT / opath(copy)).is_file():
            continue
        if open_only and any((ROOT / opath(x)).is_file() for x in after):
            continue
        out[copy] = {"module": copy, "twin": r[3], "class": r[4], "depth": r[5], "after": after,
                     "consumers": [x for x in r[7].split() if x and x != "-"], "nodes": r[8], "api": r[9]}
    return out


def blocked(g=None, imports=None, rows=None) -> tuple[set[str], set[str], dict[str, str]]:
    """(blocked node ids, blocked library modules, why: item -> the rework module it waits for).
    Nodes: the nodes realized by a rework module and every node whose stmt_deps/proof_deps (and proof-step `uses`)
    reach one, transitively. Modules: library modules importing a rework module transitively, and the modules of the
    blocked nodes (a stage-3 item whose proof needs a broken dependency)."""
    rows = load() if rows is None else rows
    if not rows:
        return set(), set(), {}
    import dag_queue
    if g is None:
        g = dag_queue.Dag(dag_queue.load())
    if imports is None:
        _, imports = li.scan()
    R = set(rows)
    why: dict[str, str] = {}
    # module level: reverse imports from the rework modules
    rev = collections.defaultdict(set)
    for m, ims in imports.items():
        for i in ims:
            rev[i].add(m)
    mods, st = set(), [(m, m) for m in R]
    while st:
        x, src = st.pop()
        for p in rev.get(x, ()):
            if p not in mods and p not in R:
                mods.add(p); why.setdefault(p, src); st.append((p, src))
    # node level: reverse all-deps from the nodes realized by rework modules
    seeds = {}
    for i, d in g.live.items():
        m = dag_queue.module_of(d)
        if m in R:
            seeds[i] = m
    nrev = collections.defaultdict(set)
    for j in g.live:
        for c in g.deps(j, "all"):
            nrev[c].add(j)
    nodes = set(seeds)
    for i, m in seeds.items():
        why.setdefault(i, m)
    st = [(i, m) for i, m in seeds.items()]
    while st:
        x, src = st.pop()
        for p in nrev.get(x, ()):
            if p not in nodes:
                nodes.add(p); why.setdefault(p, src); st.append((p, src))
    for i in nodes:
        m = dag_queue.module_of(g.live[i])
        if m and m not in R:
            mods.add(m); why.setdefault(m, why.get(i, ""))
    return nodes, mods, why


def nodes_of(modules: set[str]) -> dict[str, list[str]]:
    """module -> ids of the live DAG nodes whose Lean record names it"""
    import dag_queue
    out = collections.defaultdict(list)
    for i, d in dag_queue.load().items():
        m = dag_queue.module_of(d)
        if m in modules:
            out[m].append(i)
    return out


def importer_closure(failing: set[str], imports: dict) -> set[str]:
    """the failing modules and every library module importing one of them, transitively"""
    rev = collections.defaultdict(set)
    for m, ims in imports.items():
        for i in ims:
            rev[i].add(m)
    out, st = set(failing), list(failing)
    while st:
        for p in rev.get(st.pop(), ()):
            if p not in out:
                out.add(p); st.append(p)
    return out


def drop_import_lines(text: str, gone: set[str]) -> str:
    keep = []
    for line in text.split("\n"):
        mm = re.match(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", line)
        if mm and mm.group(1) in gone:
            continue
        keep.append(line)
    return "\n".join(keep)


def git(*a, check=True):
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
    if check and r.returncode:
        raise SystemExit(f"git {' '.join(a[:3])}: {r.stderr.strip()[:300]}")
    return r.stdout


def add_import_line(text: str, m: str) -> str:
    if m in li.imports_of(text):
        return text
    lines = text.split("\n")
    last = max((i for i, l in enumerate(lines) if re.match(r"^(?:public\s+)?(?:meta\s+)?import\s", l)), default=None)
    if last is None:
        return text
    lines.insert(last + 1, f"public import {m}")
    return "\n".join(lines)


def roots_to_restore(item: str) -> dict[str, str]:
    """{root file under lean/: its text with the import line of `item` put back} for a rework item whose import lines
    were removed from root files (column `roots`). tools/batch_land.py writes them in the landing that restores the
    module, so that the build compiles it and a take-out of the landing takes the lines out again."""
    row = load().get(item)
    out = {}
    for r in filter(None, ((row or {}).get("roots") or "").split(",")):
        f = li.LEAN / f"{r}.lean"
        if f.is_file():
            old = f.read_text(); new = add_import_line(old, item)
            if new != old:
                out[f"{r}.lean"] = new
    return out


def drop_default_target(lakefile: str, name: str) -> str:
    return re.sub(r'(defaultTargets\s*=\s*\[)([^\]]*)\]', lambda m: m.group(1) + ", ".join(
        x for x in (y.strip() for y in m.group(2).split(",")) if x and x != f'"{name}"') + "]", lakefile, count=1)


def restore_solution() -> bool:
    """put "Solution" back into the Lake default targets once every module Comparator/Weil/Solution.lean imports
    (transitively) is in the library again; one landing (group S). Called by reconcile under coord/.merge.lock."""
    lf = li.LEAN / "lakefile.toml"
    t = lf.read_text()
    m = re.search(r"defaultTargets\s*=\s*\[([^\]]*)\]", t)
    if not m or '"Solution"' in m.group(1):
        return False
    _, imports = li.scan()
    sol = li.imports_of((li.LEAN / "Comparator" / "Weil" / "Solution.lean").read_text())
    need = set(sol)
    for x in sol:
        need |= li.closure(x, imports, {})
    rows = load()
    if any(x in rows for x in need) or any(x.split(".")[0] in ("Sheaf", "WeilConjectures") and not li.file_of(x).is_file()
                                           for x in need):
        return False
    import landing as ld
    with ld.tree_lock():
        new = t.replace(m.group(0), m.group(0)[:-1] + ', "Solution"]', 1)
        lf.write_text(new)
        ld.new_record("S", {"lakefile.toml": t.encode()}, "rework: Weil.Solution back in the default targets", kind="interface")
        git("add", "--", "lean/lakefile.toml")
        git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
            "rework: Weil.Solution back in the Lake default targets (its closure is out of quarantine)"
            "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", "lean/lakefile.toml", check=False)
    print("rework: Weil.Solution back in the default targets")
    return True


def reconcile(commit: bool = True) -> int:
    """Rows whose original file is in the verified main: the fix is verified green. Delete the quarantined copy and
    the row (coord/rework-done.tsv keeps the history), one bookkeeping commit under coord/.merge.lock."""
    import mergelock
    try:
        with mergelock.merge_lock():
            restore_solution()
    except Exception as e:   # noqa: BLE001
        print("restore_solution:", repr(e)[:200])
    rows = load()
    if not rows:
        return 0
    done = []
    with mergelock.merge_lock():
        rows = load()
        for m, r in sorted(rows.items()):
            ok = subprocess.run(["git", "cat-file", "-e", f"{VERIFIED_REF}:{opath(m)}"], cwd=ROOT,
                                capture_output=True).returncode == 0
            for root in filter(None, (r.get("roots") or "").split(",")):   # compiled: its root imports it again
                rt = subprocess.run(["git", "show", f"{VERIFIED_REF}:lean/{root}.lean"], cwd=ROOT, capture_output=True, text=True)
                ok = ok and rt.returncode == 0 and m in li.imports_of(rt.stdout)
            if ok and landed(m):
                done.append(m)
        if not done:
            return 0
        stamp = time.strftime("%FT%TZ", time.gmtime())
        with open(DONE, "a") as f:
            for m in done:
                r = rows.pop(m)
                f.write("\t".join([m, r.get("sync", ""), r.get("time", ""), stamp,
                                   git("rev-parse", "--short=10", VERIFIED_REF).strip()]) + "\n")
                q = ROOT / (r.get("quarantine") or qpath(m))
                if q.is_file():
                    git("rm", "-q", "--cached", "--ignore-unmatch", "--", str(q.relative_to(ROOT)), check=False)
                    q.unlink()
        save(rows)
        if commit:
            git("add", "--", "coord/rework.tsv", "coord/rework-done.tsv")
            git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
                f"rework: {len(done)} item(s) verified green, quarantined copies removed: " + ", ".join(done)[:300]
                + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>",
                "--", "coord/rework.tsv", "coord/rework-done.tsv", *[r for r in (qpath(m) for m in done)], check=False)
    print(f"rework: {len(done)} item(s) verified green and closed: {' '.join(done)}")
    return len(done)


TRIED = ROOT / "local" / "rework-tried.json"   # module -> blob of the quarantined text autorestore compiled without success


def autorestore(workers: int = 4, limit: int = 60, recheck: bool = False) -> int:
    """The human, 2026-10-20: once a root is back, its dependents are no longer the cluster worker's job. Every rework
    module that imports no open rework module any more (a new root) and that no group has claimed is compiled as it
    is, alone, against the last green build (tools/lean_file.sh, 60 s, private mirror RW); those that compile go back
    to their original paths in ONE landing (group S) with their root import lines, verified by the next build and closed
    by `reconcile`; the others stay rework items with their own error as `cause` (each its own item, in parallel).
    A quarantined text is compiled at most once (local/rework-tried.json). Run by ~/cc1/buildloop.sh after a green build."""
    import concurrent.futures, hashlib, json, os, shutil
    import landing as ld, mergelock
    rows = load()
    live = {m for m in rows if not landed(m)}
    if not live:
        return 0
    rimp = {m: i & live for m, i in rework_imports({m: rows[m] for m in live}).items()}
    try:
        tried = json.loads(TRIED.read_text())
    except (OSError, ValueError):
        tried = {}
    def blob(m):
        p = ROOT / (rows[m].get("quarantine") or qpath(m))
        return hashlib.sha1(p.read_bytes()).hexdigest() if p.is_file() else None
    claimed = lambda m: (ROOT / "coord" / "claims" / (m + ".lock")).is_file()   # noqa: E731
    cand = sorted(m for m in live if not (rimp.get(m, set()) - {m}) and not claimed(m)
                  and tried.get(m) != blob(m) and (not (rows[m].get("cause") or "").startswith("error:")
                                                   or (recheck and "no message located" in rows[m].get("cause", ""))))[:limit]
    if not cand:
        return 0
    box = li.LEAN / ".sandbox" / "rework"
    def compile_one(m):
        rel = opath(m)[5:]
        dst = box / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / (rows[m].get("quarantine") or qpath(m)), dst)
        r = subprocess.run(["bash", str(ROOT / "tools" / "lean_file.sh"), str(dst)], cwd=ROOT, capture_output=True, text=True,
                           env=dict(os.environ, SHEAF_GROUP="RW"), timeout=900)
        out = r.stdout + r.stderr
        lines = out.splitlines()
        k = next((i for i, l in enumerate(lines) if ": error" in l or l.startswith("error")), None)
        good = r.returncode == 0 and k is None
        if good:
            return m, True, ""
        msg = " | ".join(x.strip() for x in lines[k:k + 4]) if k is not None else (lines[-1] if lines else "?")
        return m, False, msg.replace(str(box) + "/", "")
    t = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(compile_one, cand))
    ok = [m for m, good, _ in res if good]
    bad = {m: e for m, good, e in res if not good}
    with mergelock.merge_lock():
        rows = load()
        paths = ["coord/rework.tsv"]
        if ok:
            with ld.tree_lock():
                prev = {}
                for m in ok:
                    rel = opath(m)[5:]
                    if (li.LEAN / rel).exists():
                        continue
                    prev[rel] = None
                    (li.LEAN / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ROOT / (rows[m].get("quarantine") or qpath(m)), li.LEAN / rel)
                    for rr, text in roots_to_restore(m).items():
                        if rr not in prev:
                            prev[rr] = (li.LEAN / rr).read_bytes()
                        (li.LEAN / rr).write_text(add_import_line((li.LEAN / rr).read_text(), m))
                if prev:
                    ld.new_record("S", prev, "rework autorestore: quarantined modules that compile as they are, back in the library",
                                  kind="interface")
                    paths += ["lean/" + r for r in prev]
        for m, e in bad.items():
            if m in rows:
                rows[m]["cause"] = ("error: " + re.sub(r"\s+", " ", e))[:300]
            tried[m] = blob(m)
        save(rows)
        TRIED.write_text(json.dumps(tried))
        git("add", "-A", "--", *paths)
        git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
            f"rework autorestore: {len(ok)} module(s) compile as they are and go back, {len(bad)} stay with their own error"
            + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *paths, check=False)
    print(f"rework autorestore: {len(cand)} new root(s) compiled in {time.time() - t:.0f} s; {len(ok)} back in the library, "
          f"{len(bad)} stay rework items with their own error")
    return len(ok)


def main() -> int:
    a = sys.argv[1:]
    cmd = a[0] if a else "status"
    if cmd == "reconcile":
        reconcile(); return 0
    if cmd == "autorestore":
        autorestore(workers=int(a[a.index("--workers") + 1]) if "--workers" in a else 4,
                    limit=int(a[a.index("--limit") + 1]) if "--limit" in a else 60,
                    recheck="--recheck-unlocated" in a); return 0
    if cmd == "status":
        t = time.time()
        rows = load()
        _, imports = li.scan()
        op = [c["item"] for c in clusters(rows)]
        cl = clusters(rows)
        print(f"clusters: {len(cl)}; sizes " + ", ".join(str(len(c["members"])) for c in cl[:30]))
        nodes, mods, _ = blocked(None, imports, rows)
        print(f"rework items: {len(rows)}; open {len(op)}; fix landed (waiting for a green build) "
              f"{sum(1 for m in rows if landed(m))}; waiting for deeper rework {len(rows) - len(op) - sum(1 for m in rows if landed(m))}")
        print(f"blocked by rework: {len(nodes)} DAG nodes, {len(mods)} library modules ({time.time() - t:.1f} s)")
        for m in op[:40]:
            print("  open", m, "|", rows[m]["cause"][:120])
        return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
