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
  tools/rework.py release-held [--dry-run]  release the claims on held items (quarantined non-items, rule-4 blocked),
                                      write coord/rework-hold.txt for the dispatcher
  tools/rework.py cluster-restore [--dry-run]  put back every quarantined module no unfixed root blocks, in ONE
                                      landing; the global build verifies them together; failures (and importers) go
                                      back to quarantine as rework roots with their own error
  tools/rework.py autorestore [--recheck-errors]  bulk and transitive: compile every quarantined module whose imports
                                      are all back, level by level; restore those that compile in one landing per level,
                                      give the others their own error (separate items)
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


def clusters(rows=None, held: set | None = None) -> list[dict]:
    """The rework items (the human, 2026-10-20; corrected by the coordinator 2026-10-20 21:55): ONE item per root. A
    root is a quarantined module whose fix has not landed and that imports no other open rework module. Its worker
    fixes the root and adapts only the uses of the root declarations its fix changes; every other quarantined module
    (an importer, also one shared by several roots) is assigned to no worker: tools/rework.py autorestore retries it
    after green builds and it becomes an item of its own when it is a root that still fails. Roots used to be merged
    when their importers overlapped: 65 independent roots became one 2,208-member item held by a single worker.
    [{item: the root, roots: [root], members: [root], waiting: quarantined importers}], most importers first; a root
    in `held` waits for a priority retire item."""
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
    def waiting(r):
        seen, st = {r}, [r]
        while st:
            for p in rev.get(st.pop(), ()):
                if p not in seen:
                    seen.add(p); st.append(p)
        return len(seen) - 1
    out = [{"item": r, "roots": [r], "members": [r], "waiting": waiting(r)}
           for r in roots if held is None or r not in held]
    return sorted(out, key=lambda c: (-c["waiting"], c["item"]))


RETIRE = ROOT / "coord" / "retire-items.tsv"
# coord/retire-items.tsv (the human, 2026-10-20; hand-off of the twin-retirement agent, coord/changes/
# retire-sheaf-twins-20261020.md "Hand-off"): one Sheaf copy to retire per row, columns item, kind (`retire`), copy, twin,
# class, depth, after (copies to retire first, space-separated), consumers, DAG nodes, API difference. The queue item is
# the copy's module name (kind `retire`, after the rework items, before every other queue). Open when every `after` copy
# is gone from lean/; done when the copy is deleted (verified when refs/heads/sheaf-verified no longer has it).


def _present(m: str) -> bool:
    """the module is in lean/ and not a withdrawn stub (deliver3.py withdraws a module by emptying it; 2026-10-20: a
    retirement that had landed as the stub kept its retire item open and was dispatched again and again)"""
    f = ROOT / opath(m)
    if not f.is_file():
        return False
    try:
        t = f.read_text(errors="ignore")
    except OSError:
        return True
    return not (len(t) < 200 and "Withdrawn: no declarations remain." in t)


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
        if not _present(copy):
            continue
        if open_only and any(_present(x) for x in after):
            continue
        out[copy] = {"module": copy, "twin": r[3], "class": r[4], "depth": r[5], "after": after,
                     "consumers": [x for x in r[7].split() if x and x != "-"], "nodes": r[8], "api": r[9]}
    return out


COLLISION = re.compile(r"import (\S+) failed, environment already contains .*? from (\S+?)(?:\s|\||$)")


def collision_copies(cause: str) -> set[str]:
    """the Sheaf copies named in a twin-collision error (`import X failed, environment already contains ... from Y`)"""
    out = set()
    for a, b in COLLISION.findall(cause or ""):
        out |= {x.rstrip("|,.") for x in (a, b) if x.startswith("Sheaf.")}
    return out


def priority_retire(rows=None) -> tuple[dict[str, int], set[str]]:
    """The coordinator, 2026-10-20: a retire item whose copy appears in the cause of a rework root ranks ahead of every
    rework cluster, by the number of roots it unblocks; those roots are held until the copy is gone (then autorestore
    compiles them again). Returns ({copy: roots unblocked}, held roots)."""
    rows = load() if rows is None else rows
    live = {m for m in rows if not landed(m)}
    rimp = {m: i & live for m, i in rework_imports({m: rows[m] for m in live}).items()}
    retire = retire_rows(open_only=False)
    score, held = collections.Counter(), set()
    for m in live:
        if rimp.get(m, set()) - {m}:
            continue
        cps = {c for c in collision_copies(rows[m].get("cause", "")) if c in retire}
        if cps:
            held.add(m)
            for c in cps:
                score[c] += 1
    return dict(score), held


def stale_cause(m: str, rows: dict) -> bool:
    """the cause names a module (a collision partner) that is no longer in lean/: compile the module again"""
    return any(not (ROOT / opath(x)).is_file() for x in collision_copies(rows[m].get("cause", "")))


def blocked(g=None, imports=None, rows=None) -> tuple[set[str], set[str], dict[str, str]]:
    """(blocked node ids, blocked library modules, why: item -> the rework module it waits for).
    Nodes: the nodes realized by a rework module and every node whose stmt_deps/proof_deps (and proof-step `uses`)
    name one directly (2026-10-21; before: transitively). Modules: library modules importing a rework module transitively, and the modules of the
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
    # 2026-10-21 (the human: no meaningless rigor): only the DIRECT dependents of a quarantined node are blocked (their
    # dependency has no statement in the library); a node whose dependencies all have their statement in the library is
    # workable whatever lies below them. The transitive closure held 174 of 204 stage-3 items with every dependency stated.
    for x, src in seeds.items():
        for p in nrev.get(x, ()):
            if p not in nodes:
                nodes.add(p); why.setdefault(p, src)
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
    try:
        import subprocess as _sp, sys as _sy
        _sp.run([_sy.executable, str(ROOT / 'tools' / 'queue_mark.py'), 'done', '3', *done], capture_output=True, timeout=120)
    except Exception:
        pass
    print(f"rework: {len(done)} item(s) verified green and closed: {' '.join(done)}")
    return len(done)


HOLD = ROOT / "coord" / "rework-hold.txt"


def hold_set(rows=None) -> tuple[set[str], dict[str, str], set[str]]:
    """(items that are no work while the rework runs, why: item -> the rework module it waits for, the open rework
    items). Held: every quarantined module that is not the item of an open cluster (one worker restores a whole
    cluster through its item; a member or a root held for a retire item has no compiled imports to work against),
    and every node/module blocked by rework (rule 4)."""
    rows = load() if rows is None else rows
    if not rows:
        return set(), {}, set()
    first, held_roots = priority_retire(rows)
    items = {c["item"] for c in clusters(rows, held_roots)
             if (rows[c["item"]].get("cause") or "").startswith("error:")}
    items |= set(first)   # retire-first items are queued even when blocked (tools/queue.py): never held
    nodes, mods, why = blocked(None, None, rows)
    hold = (set(m for m in rows if not landed(m)) | nodes | mods) - items
    # 2026-10-21 (the human): a node owed to stage 1 (a re-split in words) is never held by a Lean rework
    import dag_queue as dq
    hold -= {n for n in nodes if dq.stage1_repair_owed(n)}
    for m in rows:
        why.setdefault(m, m)
    return hold, why, items


def release_held(apply: bool = True) -> int:
    """2026-10-20 (BLOCKED storm after the quarantine): claims taken before the sync on items that are now held
    (hold_set) kept being dispatched; their workers cannot compile (a quarantined import has no olean in the published
    build) and answered BLOCKED, then were restarted as repairs, in a loop. Release every such claim: drop its return
    entries, archive its delivery branch at refs/superseded/<group>/<item>/<head> (the item is not abandoned: it comes
    back to the queue when its rework lands), delete the claim. Writes coord/rework-hold.txt (item TAB rework module it
    waits for), which the dispatcher reads to start no worker on a held item. Returns the number released."""
    import claim
    rows = load()
    hold, why, _ = hold_set(rows)
    tmp = HOLD.with_suffix(".tmp")
    tmp.write_text("# items held while their rework runs (tools/rework.py release-held): item<TAB>quarantined module\n"
                   + "".join(f"{m}\t{why.get(m, '')}\n" for m in sorted(hold)))
    tmp.replace(HOLD)
    out, touched = [], set()
    for lk in sorted(claim.C.glob("*.lock")):
        m = lk.stem.replace("__", "/")
        if m not in hold:
            continue
        r = claim.read(m)
        if not r:
            continue
        who = r.get("who", "")
        if who in ("L", "ORCHESTRA"):
            continue
        ref = f"refs/heads/deliver/{who}/{m}"
        h = subprocess.run(["git", "rev-parse", "-q", "--verify", ref], cwd=ROOT, capture_output=True, text=True)
        rp = claim.RETURNS / f"{who}.md"
        returned = rp.is_file() and f"\n## {m} (" in "\n" + rp.read_text()
        if h.returncode == 0 and not returned:
            continue      # delivered and not returned: no worker runs on it; the lander judges the delivery
        out.append((who, m))
        if not apply:
            continue
        if claim.drop_return_entries(who, m):
            touched.add(claim.RETURNS / f"{who}.md")
        if h.returncode == 0:
            head = h.stdout.strip()
            git("update-ref", f"refs/superseded/{who}/{m}/{head}", head)
            git("update-ref", "-d", ref, head)
        lk.unlink(missing_ok=True)
        claim.log(f"{who} released {m}: held by rework (waits for {why.get(m, '?')}); released by tools/rework.py release-held"
                  + (f", delivery archived at refs/superseded/{who}/{m}/{head}" if h.returncode == 0 else ""))
    if touched:
        claim.commit_bookkeeping(sorted(touched), f"rework: return entries of {len(out)} held item(s) dropped (tools/rework.py release-held)")
    print(f"rework hold: {len(hold)} items held; claims {'released' if apply else 'to release'}: {len(out)}"
          + ("" if not out else " (" + ", ".join(f"{w} {m}" for w, m in out[:12]) + (" ..." if len(out) > 12 else "") + ")"))
    return len(out)


TRIED = ROOT / "local" / "rework-tried.json"   # module -> blob of the quarantined text autorestore compiled without success
TRIED_BUILD = ROOT / "local" / "rework-tried-build.json"   # module -> published build commit of its last failed compile
RESTORED = ROOT / "local" / "rework-restored.json"   # module -> [blob, times restored by autorestore]
MISSING_OLEAN = re.compile(r"object file .* does not exist|unknown module prefix|file not found|No such file", re.I)


def _published() -> str:
    import json
    try:
        return json.loads((ROOT / "local" / "builds" / "published.json").read_text()).get("commit") or ""
    except (OSError, ValueError):
        return ""


def autorestore(workers: int = 24, limit: int = 2000, recheck: bool = False, recheck_errors: bool = False,
                max_levels: int = 30, from_loop: bool = False) -> int:
    """Bulk, transitive autorestore (the coordinator, 2026-10-21; it used to compile 1-4 new roots per run while 2,035
    importers stayed quarantined). Each run, level by level: EVERY quarantined module that imports no other quarantined
    module any more (all its project imports are in lean/) and that no group has claimed is compiled as it is against
    the last green build (tools/lean_file.sh, group RW, `workers` in parallel). Those that compile go back to their
    original paths with their root import lines in ONE landing (group S, one record and one commit per level, verified
    by the next build and closed by `reconcile`; a red build takes the record out as any landing); the others become
    rework roots with their own error (`cause`, each its own item). The restored files are then compiled in place in
    group RW, which writes their .olean into the private mirror local/build/RW, so the next level (their importers) is
    compiled in the same run. A module an import of which has no .olean yet (landed by someone else after the last
    published build) waits for the next run. A quarantined text that failed is compiled again only when its cause is
    stale (collision partner gone) or, with recheck_errors (the timer run), once per published build. A text restored
    twice and taken out both times stays a rework item. Run by ~/cc1/buildloop.sh after a green build and by
    ~/cc1/rework-autorestore-loop.sh every 10 minutes (flock local/rework-autorestore.lock)."""
    import concurrent.futures, hashlib, json, os, shutil
    import landing as ld, mergelock
    def jload(p):
        try:
            return json.loads(p.read_text())
        except (OSError, ValueError):
            return {}
    tried, tried_build, restored = jload(TRIED), jload(TRIED_BUILD), jload(RESTORED)
    box = li.LEAN / ".sandbox" / "rework"
    M = ROOT / "local" / "build" / "RW"
    shared = li.LEAN / ".lake" / "build" / "lib" / "lean"
    env = dict(os.environ, SHEAF_GROUP="RW")
    total_ok = total_bad = 0
    T0 = time.time()

    def has_olean(i: str) -> bool:
        rel = pathlib.Path(*i.split(".")).with_suffix(".olean")
        return (M / rel).exists() or (shared / rel).exists()

    def run_lean(path):
        r = subprocess.run(["bash", str(ROOT / "tools" / "lean_file.sh"), str(path)], cwd=ROOT, capture_output=True,
                           text=True, env=env, timeout=900)
        return r.returncode, r.stdout + r.stderr

    def compile_one(m, rows):
        rel = opath(m)[5:]
        dst = box / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / (rows[m].get("quarantine") or qpath(m)), dst)
        rc, out = run_lean(dst)
        lines = out.splitlines()
        k = next((i for i, l in enumerate(lines) if ": error" in l or l.startswith("error")), None)
        if rc == 0 and k is None:
            return m, "ok", ""
        msg = " | ".join(x.strip() for x in lines[k:k + 4]) if k is not None else (lines[-1] if lines else "?")
        msg = msg.replace(str(box) + "/", "")
        if MISSING_OLEAN.search(msg) and "environment already contains" not in msg:
            return m, "wait", msg
        return m, "bad", msg

    for level in range(1, max_levels + 1):
        if (not from_loop and (ROOT / "local" / "rework-autorestore.stop").exists()) or time.time() - T0 > 1200:
            print(f"rework autorestore: stopping before level {level} (stop file or 20-min budget)", flush=True)
            break
        rows = load()
        live = {m for m in rows if not landed(m)}
        if not live:
            break
        pub = _published()
        rimp = {m: i & live for m, i in rework_imports({m: rows[m] for m in live}).items()}
        def blob(m):
            p = ROOT / (rows[m].get("quarantine") or qpath(m))
            return hashlib.sha1(p.read_bytes()).hexdigest() if p.is_file() else None
        claimed = lambda m: (ROOT / "coord" / "claims" / (m + ".lock")).is_file()   # noqa: E731
        cand, waiting = [], 0
        for m in sorted(live):
            if rimp.get(m, set()) - {m} or claimed(m):
                continue
            b = blob(m)
            if b is None:
                continue
            rs = restored.get(m)
            if rs and rs[0] == b and rs[1] >= 2:
                continue        # restored twice with this text and taken out both times
            cause = rows[m].get("cause") or ""
            if cause.startswith("error:"):
                if not (stale_cause(m, rows) or (recheck and "no message located" in cause)
                        or tried.get(m) != b or (recheck_errors and tried_build.get(m) != pub)):
                    continue
            elif tried.get(m) == b and tried_build.get(m) == pub:
                continue
            q = ROOT / (rows[m].get("quarantine") or qpath(m))
            proj = [i for i in li.imports_of(q.read_text(errors="ignore")) if li.file_of(i).is_file()]
            if not all(has_olean(i) for i in proj):
                waiting += 1
                continue
            cand.append(m)
        cand = cand[:limit]
        if not cand:
            if level == 1:
                print(f"rework autorestore: nothing to compile ({len(live)} quarantined, {waiting} wait for .oleans)")
            break
        t = time.time()
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            res = list(ex.map(lambda m: compile_one(m, rows), cand))
        ok = [m for m, s, _ in res if s == "ok"]
        bad = {m: e for m, s, e in res if s == "bad"}
        wait = [m for m, s, _ in res if s == "wait"]
        tc = time.time() - t
        restored_now = []
        with mergelock.merge_lock():
            rows = load()
            paths = ["coord/rework.tsv"]
            if ok:
                with ld.tree_lock():
                    prev = {}
                    for m in ok:
                        rel = opath(m)[5:]
                        if (li.LEAN / rel).exists() or m not in rows:
                            continue
                        prev[rel] = None
                        (li.LEAN / rel).parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(ROOT / (rows[m].get("quarantine") or qpath(m)), li.LEAN / rel)
                        restored_now.append(m)
                        b = blob(m)
                        rs = restored.get(m)
                        restored[m] = [b, (rs[1] + 1) if rs and rs[0] == b else 1]
                        for rr, text in roots_to_restore(m).items():
                            if rr not in prev:
                                prev[rr] = (li.LEAN / rr).read_bytes()
                            (li.LEAN / rr).write_text(add_import_line((li.LEAN / rr).read_text(), m))
                    if prev:
                        ld.new_record("S", prev, f"rework autorestore level {level}: {len(restored_now)} quarantined "
                                      "module(s) that compile as they are, back in the library", kind="interface")
                        paths += ["lean/" + r for r in prev]
            for m, e in bad.items():
                if m in rows:
                    rows[m]["cause"] = ("error: " + re.sub(r"\s+", " ", e))[:300]
                tried[m] = blob(m); tried_build[m] = pub
            save(rows)
            TRIED.write_text(json.dumps(tried)); TRIED_BUILD.write_text(json.dumps(tried_build))
            RESTORED.write_text(json.dumps(restored))
            git("add", "-A", "--", *paths)
            git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
                f"rework autorestore (level {level}): {len(restored_now)} module(s) compile as they are and go back, "
                f"{len(bad)} stay with their own error"
                + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *paths, check=False)
        total_ok += len(restored_now); total_bad += len(bad)
        # the next level imports these: their .olean into the RW mirror (in place, now that they are in lean/)
        t2 = time.time()
        if restored_now:
            with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
                built = list(ex.map(lambda m: run_lean(ROOT / opath(m))[0], restored_now))
            nb = sum(1 for x in built if x != 0)
        else:
            nb = 0
        print(f"{time.strftime('%F %T')} rework autorestore level {level}: {len(cand)} compiled in {tc:.0f} s; "
              f"{len(restored_now)} back in the library, {len(bad)} stay rework items with their own error, "
              f"{len(wait)} wait for .oleans; mirror .oleans in {time.time() - t2:.0f} s"
              + (f" ({nb} failed in place)" if nb else ""), flush=True)
        if not restored_now:
            break
    print(f"{time.strftime('%F %T')} rework autorestore: {total_ok} back, {total_bad} new error roots in "
          f"{time.time() - T0:.0f} s; quarantined now {sum(1 for m in load() if not landed(m))}", flush=True)
    return total_ok


CLUSTER_LOG = ROOT / "local" / "rework-cluster.json"
PROJECT_PREFIXES = ("Sheaf.", "WeilConjectures.", "Comparator.", "Weil.")


def cluster_set(rows=None) -> tuple[list[str], set[str]]:
    """(the modules a cluster restore puts back, the blocked seeds). Seeds: quarantined modules whose fix has not
    landed and that are error roots (`cause` error:). Everything quarantined that imports no
    seed, transitively through quarantined modules, and no project module that exists neither in lean/ nor in the
    restore set, comes back."""
    rows = load() if rows is None else rows
    live = {m for m in rows if not landed(m)}
    allimp = rework_imports({m: rows[m] for m in live})
    # an importer's claim (a delivery from before the quarantine, waiting) does not block: only roots CONFIRMED unfixed
    # do: an error root whose quarantined text is the one that failed (local/rework-tried.json) and whose error does not
    # name a collision partner that is gone. A root never compiled with its present text is put back too: the build decides.
    import hashlib, json
    try:
        tried = json.loads(TRIED.read_text())
    except (OSError, ValueError):
        tried = {}
    def blob(m):
        p = ROOT / (rows[m].get("quarantine") or qpath(m))
        return hashlib.sha1(p.read_bytes()).hexdigest() if p.is_file() else None
    seeds = {m for m in live if (rows[m].get("cause") or "").startswith("error:")
             and tried.get(m) == blob(m) and not stale_cause(m, rows)}
    bad = set(seeds)
    for m in live:     # a project import that is nowhere (neither in lean/ nor quarantined)
        if any(i.startswith(PROJECT_PREFIXES) and i not in live and not li.file_of(i).is_file() for i in allimp[m] - {m}):
            bad.add(m)
    rev = collections.defaultdict(set)
    for m in live:
        for i in allimp[m] & live:
            if i != m:
                rev[i].add(m)
    st = list(bad)
    while st:
        for p in rev.get(st.pop(), ()):
            if p not in bad:
                bad.add(p); st.append(p)
    return sorted(live - bad), seeds


def _wait_build(rid: str, seen: set, timeout: float = 7200) -> dict:
    """the first global build (local/builds/last.json) whose landings include the record `rid`"""
    import json
    t0 = time.time()
    last = None
    while time.time() - t0 < timeout:
        try:
            d = json.loads((ROOT / "local" / "builds" / "last.json").read_text())
        except (OSError, ValueError):
            d = {}
        if d.get("time") != last:
            last = d.get("time")
            if d.get("time") not in seen and (rid in (d.get("verified") or []) or rid in (d.get("included") or [])):
                seen.add(d.get("time"))
                return d
        time.sleep(15)
    return {}


def _first_errors(failing: set[str]) -> dict[str, str]:
    out = {}
    try:
        text = (ROOT / "local" / "build.log").read_text(errors="ignore")
    except OSError:
        return out
    paths = {m: m.replace(".", "/") + ".lean" for m in failing}
    for line in text.splitlines():
        if "error" not in line:
            continue
        for m, p in paths.items():
            if m not in out and p in line:
                out[m] = re.sub(r"\s+", " ", line.strip())[:300]
    return out


def _drop_mine(ids: list[str], reason: str) -> list[dict]:
    """take my open restore landings `ids` out of the candidate (merge queue: ld.drop_plan, files back to their version
    before the landing, one commit, records closed as reverted). Caller holds coord/.merge.lock."""
    import landing as ld
    with ld.tree_lock():
        open_ids = {r["id"] for r in ld.records(ld.REQUESTS)}
        ids = [i for i in ids if i in open_ids]
        if not ids:
            return []
        dropped, restore_to, notes = ld.drop_plan(ids)
        paths = []
        for rel, data in restore_to.items():
            f = li.LEAN / rel
            if data is None:
                f.unlink(missing_ok=True)
            else:
                f.parent.mkdir(parents=True, exist_ok=True); f.write_bytes(data)
            paths.append("lean/" + rel)
        for i in range(0, len(paths), 400):
            git("add", "-A", "--", *paths[i:i + 400])
        git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
            f"rework cluster restore: {len(dropped)} landing(s) taken out of the candidate ({reason[:200]})"
            "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *paths, check=False)
        ld.drop_close(dropped, reason)
    return dropped


PENDING = ROOT / "local" / "rework-cluster-pending.json"


def _failing_of(rid: str) -> set:
    """the modules the build that reverted landing `rid` named failing (from its closed record)"""
    import json
    try:
        r = json.loads((ROOT / "local" / "builds" / "done" / f"{rid}.json").read_text()).get("reason", "")
    except (OSError, ValueError):
        return set()
    return set(re.findall(r"[A-Z][\w.]+", r.split("failed in", 1)[1])) if "failed in" in r else set()


def settle_restores() -> None:
    """Restored modules whose landing the merge queue reverted (file gone again from lean/) are put back in quarantine:
    their quarantined text is marked tried (so the next cluster restore does not put them back unchanged; the level-wise
    recheck compiles them again once per published build). Landings verified green are forgotten."""
    import hashlib, json
    import landing as ld
    try:
        pend = json.loads(PENDING.read_text())
    except (OSError, ValueError):
        return
    open_ids = {r["id"] for r in ld.records(ld.REQUESTS)}
    rows = load()
    try:
        tried = json.loads(TRIED.read_text())
    except (OSError, ValueError):
        tried = {}
    keep, back = {}, 0
    for m, rid in pend.items():
        if rid in open_ids:
            keep[m] = rid; continue
        if (ROOT / opath(m)).is_file():
            continue                       # verified (or still in): reconcile closes the row
        q = ROOT / ((rows.get(m) or {}).get("quarantine") or qpath(m))
        # 2026-10-21: only a module the build itself named failing is a root with its own error (marked tried); one the
        # merge queue reverted with others (collateral) stays an ordinary quarantined module and comes back with the
        # next batch once no unfixed root blocks it (1129 of 1191 were collateral and had been frozen as roots)
        if q.is_file() and m in _failing_of(rid):
            tried[m] = hashlib.sha1(q.read_bytes()).hexdigest(); back += 1
            if m in rows:
                rows[m]["cause"] = "error: failed in the global build after a cluster restore (see the build log)"
    if back:
        save(rows)
    TRIED.write_text(json.dumps(tried)); PENDING.write_text(json.dumps(keep))
    if back:
        print(f"{time.strftime('%F %T')} cluster restore settle: {back} reverted module(s) back in quarantine (marked tried)", flush=True)


def cluster_restore(rounds: int = 8, dry: bool = False, wait: bool = False) -> int:
    """The human's design (2026-10-21): put back EVERY quarantined module no confirmed-unfixed root blocks (cluster_set,
    all levels at once) in one step, without compiling them one by one; the global build verifies them together.
    One landing record PER MODULE (its file, and its root import lines), all in one commit: a red build then takes out
    only what fails (the merge queue drops landings whose own modules fail: tools/batch_land.py, and this function
    itself) instead of the whole restore. Red: the failing restored modules and their restored importers
    (transitively) are taken out at once; the failing ones become rework roots with their own error (and their text is
    marked tried), the importers keep `imports X`. Repeat until a build verifies the rest (at most `rounds` builds)."""
    import hashlib, json, shutil
    import landing as ld, mergelock
    T0 = time.time()
    settle_restores()
    rows = load()
    put, seeds = cluster_set(rows)
    print(f"{time.strftime('%F %T')} cluster restore: {len(put)} quarantined module(s) to put back "
          f"({len(seeds)} confirmed unfixed roots block {sum(1 for m in rows if not landed(m)) - len(put)})", flush=True)
    if dry or not put:
        return len(put)
    rec_of: dict[str, str] = {}
    with mergelock.merge_lock():
        rows = load()
        paths = set()
        with ld.tree_lock():
            for m in put:
                rel = opath(m)[5:]
                src = ROOT / (rows[m].get("quarantine") or qpath(m))
                if (li.LEAN / rel).exists() or not src.is_file():
                    continue
                prev = {rel: None}
                (li.LEAN / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, li.LEAN / rel)
                for rr in filter(None, (rows[m].get("roots") or "").split(",")):
                    f = li.LEAN / f"{rr}.lean"
                    if f.is_file():
                        old = f.read_bytes(); new = add_import_line(old.decode(), m)
                        if new != old.decode():
                            prev[f"{rr}.lean"] = old; f.write_text(new)
                r = ld.new_record("S", prev, f"rework cluster restore: {m} back from quarantine (verified with its cluster "
                                  "by the global build)", kind="proof")
                rec_of[m] = r["id"]
                paths |= {"lean/" + x for x in prev}
        paths = sorted(paths)
        for i in range(0, len(paths), 400):
            git("add", "-A", "--", *paths[i:i + 400])
        git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
            f"rework cluster restore: {len(rec_of)} quarantined module(s) back in the library in one step (every module "
            "no confirmed-unfixed root blocks, all levels; one landing record per module; the global build verifies them)"
            "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", *paths, check=False)
    restored = set(rec_of)
    print(f"{time.strftime('%F %T')} cluster restore: {len(restored)} module(s) put back ({len(rec_of)} landings, one commit)",
          flush=True)
    if not wait:
        # the human, 2026-10-21: no waiting for the build; settle_restores() at the next run reads what the merge queue
        # reverted and puts those modules back in quarantine
        pend = {}
        try:
            pend = json.loads(PENDING.read_text())
        except (OSError, ValueError):
            pend = {}
        pend.update(rec_of); PENDING.write_text(json.dumps(pend))
        print(f"{time.strftime('%F %T')} cluster restore: not waiting for the build ({len(rec_of)} landing(s) pending)", flush=True)
        return len(restored)
    state = {"start": time.strftime("%FT%TZ", time.gmtime()), "restored": len(restored), "builds": []}
    out: dict[str, str] = {}          # module -> cause, taken out again
    seen: set = set()
    for k in range(1, rounds + 1):
        open_ids = {r["id"] for r in ld.records(ld.REQUESTS)}
        mine = {m: i for m, i in rec_of.items() if i in open_ids}
        if not mine:
            break
        tb = time.time()
        d = {}
        while time.time() - tb < 7200:
            try:
                d = json.loads((ROOT / "local" / "builds" / "last.json").read_text())
            except (OSError, ValueError):
                d = {}
            if d.get("time") not in seen and set(mine.values()) & set((d.get("verified") or []) + (d.get("included") or [])):
                seen.add(d.get("time")); break
            d = {}
            time.sleep(5)
        if not d:
            print("cluster restore: no build took the landings within 2 h; stopping", flush=True); break
        state["builds"].append({"result": d.get("result"), "seconds": d.get("seconds"), "waited": round(time.time() - tb)})
        print(f"{time.strftime('%F %T')} cluster restore build {k}: {d.get('result')} in {d.get('seconds')} s "
              f"(waited {time.time() - tb:.0f} s)", flush=True)
        if d.get("result") == "green":
            continue
        failing = set(d.get("failing") or []) & restored
        _, imports = li.scan()
        clos = (importer_closure(failing, imports) & restored) | failing
        # modules of mine the merge queue already took out (tools/batch_land.py drops a landing whose module fails)
        gone = {m for m in restored if m not in out and not (ROOT / opath(m)).is_file()}
        errs = {m: e for m, e in _first_errors(failing).items()
                if not re.search(r"bad import|unknown module|object file .* does not exist|file not found", e, re.I)}
        memo: dict = {}
        with mergelock.merge_lock():
            dropped = _drop_mine([rec_of[m] for m in clos],
                                 f"the global build of {str(d.get('commit'))[:10]} failed in {' '.join(sorted(failing)[:6])}; "
                                 "restored module or importer of one: back to quarantine")
            gone |= {m for m in restored if not (ROOT / opath(m)).is_file()}
            rows = load()
            try:
                tried = json.loads(TRIED.read_text())
            except (OSError, ValueError):
                tried = {}
            new = sorted(gone - set(out))
            for m in new:
                if m in errs or (m in failing and not (imports.get(m, set()) & gone)):
                    cause = errs.get(m) or "error: failed in the global build (no message located)"
                    q = ROOT / (rows[m].get("quarantine") or qpath(m)) if m in rows else ROOT / qpath(m)
                    if q.is_file():
                        tried[m] = hashlib.sha1(q.read_bytes()).hexdigest()
                else:
                    cause = "imports " + next(iter(sorted(li.closure(m, imports, memo) & (failing | gone))), "?")
                out[m] = cause
                if m in rows:
                    rows[m]["cause"] = cause[:300]
            save(rows); TRIED.write_text(json.dumps(tried))
            git("add", "--", "coord/rework.tsv")
            git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
                f"rework cluster restore, build {k}: {len(new)} module(s) back in quarantine "
                f"({sum(1 for m in new if out[m].startswith('error'))} with their own error)"
                "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", "coord/rework.tsv", check=False)
        print(f"{time.strftime('%F %T')} cluster restore build {k}: {len(failing)} failing; {len(new)} module(s) back in "
              f"quarantine ({len(dropped)} landing(s) dropped here, the rest by the merge queue)", flush=True)
    kept = sum(1 for m in restored if (ROOT / opath(m)).is_file())
    state.update(requarantined=len(out), kept=kept, seconds=round(time.time() - T0),
                 quarantined_after=sum(1 for m in load() if not landed(m)))
    CLUSTER_LOG.write_text(json.dumps(state, indent=1))
    print(f"{time.strftime('%F %T')} cluster restore done: {len(restored)} put back, {len(out)} back in quarantine, "
          f"{kept} stay; {state['seconds']} s; quarantined now {state['quarantined_after']}", flush=True)
    return kept


def main() -> int:
    a = sys.argv[1:]
    cmd = a[0] if a else "status"
    if cmd == "reconcile":
        reconcile(); return 0
    if cmd == "autorestore" and not ({"--level-wise", "--recheck-unlocated", "--recheck-errors"} & set(a)):
        print("rework autorestore: restores land with every batch of tools/batch_land.py (2026-10-21); nothing done here")
        return 0
    if cmd == "autorestore":
        autorestore(workers=int(a[a.index("--workers") + 1]) if "--workers" in a else 24,
                    limit=int(a[a.index("--limit") + 1]) if "--limit" in a else 2000,
                    recheck="--recheck-unlocated" in a, recheck_errors="--recheck-errors" in a, from_loop="--from-loop" in a); return 0
    if cmd == "cluster-restore":
        cluster_restore(dry="--dry-run" in a, wait="--wait" in a); return 0
    if cmd == "release-held":
        release_held(apply="--dry-run" not in a); return 0
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
