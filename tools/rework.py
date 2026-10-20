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
"""
from __future__ import annotations
import collections, datetime, pathlib, re, subprocess, sys, time

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
ROOTS_KEPT = ("Challenge",)
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


def reconcile(commit: bool = True) -> int:
    """Rows whose original file is in the verified main: the fix is verified green. Delete the quarantined copy and
    the row (coord/rework-done.tsv keeps the history), one bookkeeping commit under coord/.merge.lock."""
    rows = load()
    if not rows:
        return 0
    import mergelock
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


def main() -> int:
    a = sys.argv[1:]
    cmd = a[0] if a else "status"
    if cmd == "reconcile":
        reconcile(); return 0
    if cmd == "status":
        t = time.time()
        rows = load()
        _, imports = li.scan()
        op = open_items(rows, imports)
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
