#!/usr/bin/env python3
"""Priority roots (the human, 2026-10-25: the upstream trace formula needs some batch-5 route nodes sorry-free soon; we
deduce the upstream statements from ours). coord/priority-roots.txt lists them, one node id or module per line.

The closure of the roots is everything still open that they need to become sorry-free:
  1. their Lean route: the sorried project declarations the root modules' declarations use, through types and values
     (tools/sorry_route.py `walk`, with NO assumed declarations: the roots must be sorry-free, not sorry-free modulo
     what batch 5 assumes). The walk reads the compiled build; it is cached per published build in
     local/priority-route.json (`refresh`; tools/tag_batches.py starts it in the background when the published build is
     newer than the cache and uses the last cache meanwhile);
  2. their DAG closure: the root nodes and the nodes declaring a declaration of that route, and every node reached
     from them through stmt_deps, proof_deps and the `uses` of the proof steps, not entering a proved node (closed on
     the done branch, or its recorded module in live without `sorry`). An assumed node is entered (see 1).
The priority items are the coord/queue.tsv rows of those nodes (stages 1 and 2) and of their modules and the route
modules (stage 3). tools/tag_batches.py tags them `priority` in coord/queue-batches.tsv, except the rework, retire and
retire-first rows, which keep their own earlier lanes; the dispatcher (Codex ~/weil-launcher-all/config.json) serves the
lanes (batch1, priority) and (batch2, priority) right after `retire`, before every batch lane.

Usage:
  tools/priority.py refresh   walk the root modules on the published build, write local/priority-route.json
  tools/priority.py report    every open item of each root's closure with its state (queue row, claim, or why it waits)
"""
from __future__ import annotations
import collections, json, os, pathlib, subprocess, sys, time

R = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R / "tools"))
ROOTS = R / "coord" / "priority-roots.txt"
CACHE = R / "local" / "priority-route.json"
PUBLISHED = R / "local" / "builds" / "published.json"
LOCK = R / "local" / "priority-refresh.lock"


def roots() -> list[str]:
    try:
        lines = ROOTS.read_text().splitlines()
    except OSError:
        return []
    return [l.split("#", 1)[0].split()[0] for l in lines if l.split("#", 1)[0].strip()]


def published_commit() -> str:
    try:
        return json.loads(PUBLISHED.read_text()).get("commit") or ""
    except (OSError, ValueError):
        return ""


def resolve(g, dq, toks):
    """(root nodes, root modules): a token naming a live node gives the node and its module; a token naming a module
    gives the module and every live node recorded in it."""
    nodes, mods = set(), set()
    bymod = collections.defaultdict(set)
    for i, d in g.live.items():
        m = dq.module_of(d)
        if m:
            bymod[m].add(i)
    for t in toks:
        t = g.resolve(t)
        if t in g.live:
            nodes.add(t)
            m = dq.module_of(g.live[t])
            if m:
                mods.add(m)
        else:
            mods.add(t); nodes |= bymod.get(t, set())
    return nodes, mods


def load_cache() -> dict:
    try:
        return json.loads(CACHE.read_text())
    except (OSError, ValueError):
        return {}


def stale(mods) -> bool:
    c = load_cache()
    return c.get("tried") != published_commit() or set(c.get("walks", {})) != set(mods)


def refresh() -> int:
    """walk each root module (no assumptions) on the published build; the cache keeps the last good walk of a module
    whose walk failed"""
    import fcntl
    import dag_queue as dq
    import sorry_route
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    lk = open(LOCK, "a")
    try:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("a refresh is running"); return 0
    g = dq.Dag(dq.load())
    _, mods = resolve(g, dq, roots())
    commit, old = published_commit(), load_cache()
    # 2026-10-27: the same hold as tools/sorry_route.py: a build taken during a cluster quarantine cuts the root walks at
    # the missing modules (16:05: smoothTrace route 51 open on 7e4a2bea9b, 71 once walked on the restored build)
    hold = sorry_route.quarantine_hold(commit)
    if hold and old.get("walks"):
        old["tried"] = commit
        tmp = CACHE.with_suffix(".tmp"); tmp.write_text(json.dumps(old, indent=1) + "\n"); os.replace(tmp, CACHE)
        print(f"priority route held: {hold}; keeping the walks of {old.get('commit', '')[:10]}")
        return 0
    walks, failed = {}, []
    for m in sorted(mods):
        w = sorry_route.walk(m)
        if w is None:
            failed.append(m)
            if m in old.get("walks", {}):
                walks[m] = old["walks"][m]
            continue
        walks[m] = {k: sorted(v) for k, v in w.items()}
    # `tried`: a failed walk is not retried before the next published build (tools/tag_batches.py runs every few minutes)
    out = {"t": time.time(), "commit": commit if not failed else old.get("commit", ""), "tried": commit, "walks": walks,
           "failed": failed}
    tmp = CACHE.with_suffix(".tmp"); tmp.write_text(json.dumps(out, indent=1) + "\n"); os.replace(tmp, CACHE)
    print(f"priority route: {len(walks)} root modules walked on {commit[:10]}, failed {failed or 'none'}; "
          f"{sum(len(v) for v in walks.values())} sorried modules on their routes")
    return 1 if failed else 0


def refresh_in_background(mods) -> bool:
    """start `refresh` detached when the cache does not describe the published build (tools/tag_batches.py)"""
    if not mods or not stale(mods):
        return False
    log = R / "local" / "priority-refresh.log"
    with open(log, "a") as f:
        subprocess.Popen(["nice", "-n", "10", sys.executable, str(R / "tools" / "priority.py"), "refresh"], cwd=R,
                         stdout=f, stderr=f, stdin=subprocess.DEVNULL, start_new_session=True)
    return True


def proved(dq, d) -> bool:
    """closed on the done branch, or its recorded module in live without `sorry` (assumed nodes are not proved here)"""
    if dq.closed_upstream(d):
        return True
    m = dq.module_of(d)
    if not m:
        return False
    p = dq.li.file_of(m)
    try:
        return p.is_file() and dq.li.sorry_count(p.read_text(errors="ignore")) == 0
    except OSError:
        return False


def closure(g, dq, toks):
    """(nodes, modules) still open that `toks` need (see the module docstring); modules include the route modules"""
    rnodes, rmods = resolve(g, dq, toks)
    walks = load_cache().get("walks", {})
    route = {}   # module -> declarations, over the root modules' walks
    for m in rmods:
        for mm, ds in (walks.get(m) or {}).items():
            route.setdefault(mm, set()).update(ds)
    rdecls = {x for ds in route.values() for x in ds}
    import below_route
    db = dq.done_branch()
    start = set(rnodes) | {i for i, d in g.live.items() if rdecls and any(x in rdecls for x in below_route.decl_names(d, db))}
    # 2026-10-26 (b69, route-only): a node whose own declarations are written and sorry-free is proved too, as in the
    # progress walk (tools/progress_reach.py, own_decl.own); before, only a sorry-free MODULE stopped the walk, so the
    # closure ran below written proofs and listed modules whose sorries the roots do not use.
    from own_decl import own

    # 2026-10-26: a module quarantined by a red build (a rework row not landed back) has its proof written; its rework
    # item restores it, so the walk stops there as in tools/progress_reach.py. Going below it put ~830 off-route modules
    # on the queue as priority after the 15:57 quarantine of 3642 modules.
    try:
        import rework as _rw
        quarantined = {m for m in _rw.load() if not _rw.landed(m)}
    except Exception:  # noqa: BLE001
        quarantined = set()

    def done(d):
        m = dq.module_of(d)
        return proved(dq, d) or (bool(m) and (m in quarantined or own(d, m) is False))

    seen, st = set(), sorted(start)
    while st:
        i = st.pop()
        if i in seen or i not in g.live:
            continue
        seen.add(i)
        d = g.live[i]
        if dq.is_leaf(d) or (i not in rnodes and done(d)):
            continue
        st.extend(c for c in g.deps(i, "all") if c not in seen)
    nodes = {i for i in seen if not dq.is_leaf(g.live[i]) and not done(g.live[i])} | (rnodes & seen)
    mods = set(rmods) | set(route) | {dq.module_of(g.live[i]) for i in nodes if dq.module_of(g.live[i])}
    return nodes, mods


def items(queue_rows, g=None, dq=None) -> set[str]:
    """the queue items (coord/queue.tsv first column) of the roots' closure; `queue_rows` the item names"""
    toks = roots()
    if not toks:
        return set()
    if dq is None:
        import dag_queue as dq
    if g is None:
        g = dq.Dag(dq.load())
    nodes, mods = closure(g, dq, toks)
    return {x for x in queue_rows if x in nodes or x in mods}


def report() -> int:
    import dag_queue as dq
    g = dq.Dag(dq.load())
    q = {}
    for n, l in enumerate((R / "coord/queue.tsv").read_text().splitlines(), 1):
        r = l.split("\t")
        if not l.startswith("#") and len(r) > 4:
            q.setdefault(r[0], (n, r[1], r[4]))
    tags = {}
    for l in (R / "coord/queue-batches.tsv").read_text().splitlines():
        r = l.split("\t")
        if len(r) == 2 and not l.startswith("#"):
            tags[r[0]] = r[1]
    waiting = {}
    for m, c in g.waiting():
        waiting.setdefault(m, c)
    try:
        import rework
        rw = rework.load()
    except Exception:
        rw = {}
    pending = {}   # ~/upstream-pr/upstream-pending.tsv, as tools/queue.py upstream_pending reads it
    try:
        for l in (pathlib.Path.home() / "upstream-pr" / "upstream-pending.tsv").read_text().splitlines():
            r = l.split("\t")
            if len(r) >= 2 and not l.startswith("#"):
                pending.setdefault(r[0].strip(), r[1].strip())
    except OSError:
        pass
    def builderr(m):
        p = R / "coord" / "build-errors" / f"{m}.txt"
        try:
            t = p.read_text(errors="ignore")
        except OSError:
            return ""
        return "; build error (heartbeat/time limit)" if "timeout" in t.lower() or "timed out" in t.lower() else "; build error"
    c = load_cache()
    print(f"route cache: commit {c.get('commit', '')[:10]} (published {published_commit()[:10]}), failed {c.get('failed') or 'none'}")
    for t in roots():
        nodes, mods = closure(g, dq, [t])
        print(f"\n== {t}: {len(nodes)} open nodes, {len(mods)} modules (route and recorded)")
        for x in sorted(nodes | mods, key=lambda x: (x not in q, x)):
            claim = R / "coord" / "claims" / f"{x}.lock"
            who = ""
            if claim.exists():
                try: who = json.loads(claim.read_text()).get("who", "?")
                except (OSError, ValueError): who = "?"
            if x in q:
                n, st, kind = q[x]
                state = f"queue row {n} stage {st} {kind} tag {tags.get(x, '-')}"
            elif x in mods:
                p = dq.li.file_of(x)
                ns = dq.li.sorry_count(p.read_text(errors="ignore")) if p.is_file() else -1
                if ns <= 0 and x not in rw:
                    continue   # proved, or no live file (a Mathlib module, a module not written yet: its node is listed)
                state = (f"rework (quarantined)" if ns < 0 else
                         f"{ns} sorry, waits for the statement of {waiting[x]}" if x in waiting else
                         f"{ns} sorry, held for upstream PR {pending[x]}" if x in pending else
                         f"{ns} sorry, rework" if x in rw else f"{ns} sorry, not listed")
            else:
                d = g.live[x]
                if dq.has_decl(d):
                    continue   # stated: its module is listed
                state = ("split, not open for stage 2 (a stmt_dep unstated, or blocked by rework)" if dq.unfolded(d)
                         else "not split, not listed")
            if x in mods:
                state += builderr(x)
            print(f"  {x}\t{state}" + (f"\tclaimed by {who}" if who else ""))
    return 0


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "report"
    sys.exit(refresh() if cmd == "refresh" else report() if cmd == "report" else (print(__doc__) or 2))
