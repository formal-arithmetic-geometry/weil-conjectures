#!/usr/bin/env python3
"""The work queue: the open items of every open stage, and what the targets need. Reads sources only; no Lean is run.

Usage:
  tools/queue.py write        write coord/queue.tsv and coord/queue.md (the maintainer, after each build)
  tools/queue.py summary      how many items each stage has open, how many modules the targets need and how many still contain `sorry`
  tools/queue.py outside      modules outside the targets' import closure, one per line

Stages 1 and 2 are read from the DAG by dag_queue.py: the nodes still to split, and the nodes that can be stated
because every node their statement needs is stated. Stage 3 is read from the Lean code and the DAG: the targets are
the library modules imported by lean/TargetsCheck.lean, and a library module is an item when all of this holds
(the human, 2026-10-18: a node may be proved as soon as every statement it depends on, stmt_deps and proof_deps,
has a Lean statement, whatever its depth below the target):
  1. it still contains `sorry` or `admit`;
  2. it is on the sorry route of an open batch (local/sorry-route.json, tools/sorry_route.py: a sorried declaration
     some target actually uses; 2026-10-17), or below a route sorry of an open batch (tools/below_route.py: in the
     dependency closure of a node whose declaration is a sorry on that batch's own route, or of a target whose own
     declaration is still a sorry, within the batch's own reach, not through an assumed node, another batch's target
     or a finished node). A sorried module in the targets' import closure that is neither is bypassed by the Lean
     route and is not an item (STATE["off_route"]); a module changed after the route was computed stays an item
     until the next refresh;
  3. every node in the dependencies (stmt_deps, proof_deps and the `uses` of the proof steps) of the node(s) it
     realizes has its Lean statement: a declaration of the library, a Mathlib leaf, a finished node or a node assumed
     by its batches (coord/assumed.tsv); dag_queue.Dag.waiting/stated (the human, 2026-10-17: the prover must see what
     is available before proving). Otherwise it is listed as "waiting for statements of dependencies" until stage 2
     has stated those nodes. Exempt: a repair of a module without `sorry` (already proved, broken by an upstream change)
     and an item already claimed (coord/claims; nothing is released here);
  4. it is not listed in ~/upstream-pr/upstream-pending.tsv (the human, 2026-10-18: do not duplicate Orchestra's open
     PRs): the modules an open Orchestra branch or PR of the source library proves, written hourly from GitHub by the
     launcher's machine, outside the repository. The hold ends by itself when the module has no `sorry` left in live
     (the sync brought the proof) or when the module leaves the file; such modules are listed as "held for an open
     upstream PR" (STATE["pending"]), claimed or not.
No cap. Before every stage, the REWORK items (tools/rework.py, the human 2026-10-20): modules the scheduled upstream
sync moved out of the library because they failed to build, listed first in coord/queue.tsv as stage 3, kind
`rework`, those that import no other rework module (bottom-up); they have priority over every other queue. Any item
of stage 1, 2 or 3 whose dependencies reach a rework item (stmt_deps/proof_deps closure for nodes; imports, or a
blocked node, for modules) is left out of the queue until that item is fixed ("blocked by rework" in queue.md).
The order of stage 3 after the rework items:
  1. modules listed in coord/repairs.txt, in file order (proof or definition repairs),
  2. modules containing `STATEMENT-DISPUTED`,
  3. the rest: the modules on the route first, then by the distance to the nearest route sorry (dependency steps in
     the DAG, ascending), ties nearest to a target first (fewest import steps from a target module; a module the
     targets do not import yet last), then by name.
Without a complete route the import closure of the targets is used (STATE), as before 2026-10-17. `write` also puts
the modules below a route sorry, per batch, into local/stage3-reach.json for tools/tag_batches.py.

coord/queue.tsv lists stage 1 first, then 2, then 3. Within stage 1 the items nearest to a target come first; within
stage 2 the definitions first, then the items the most stage-2 nodes wait for through stmt_deps (the last column,
`blockers`; human, 2026-10-11 23:30 +08), ties nearest to Mathlib, counted in dependency steps down to a Mathlib leaf,
so the statements climb from Mathlib upward; stage 3 as above, its last column `route` for a module on the route and
the distance to the nearest route sorry otherwise. `claim.py next` without `--stage` takes from the head.
"""
from __future__ import annotations
import collections, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
import dag_queue  # noqa: E402

WORK = li.ROOT / "coord"
STATE = {}   # how stage 3 was selected (route or closure) and the sorried closure modules left out


def analyse():
    """imports, and the distance of every module the targets reach; empty when the targets are not stated yet."""
    if not li.LEAN.is_dir():
        return {}, {}
    _, imports = li.scan()
    roots = sorted(imports.get("TargetsCheck", set()))
    dist, dq = {}, collections.deque()
    for r in roots:
        dist[r] = 0; dq.append(r)
    while dq:
        x = dq.popleft()
        for i in imports.get(x, ()):
            if i in imports and i not in dist:
                dist[i] = dist[x] + 1; dq.append(i)
    return imports, dist


def claimed(m: str) -> bool:
    """an item some group holds (coord/claims/<module>.lock, tools/claim.py): it stays an item whatever its dependencies"""
    return (WORK / "claims" / (m.replace("/", "__") + ".lock")).is_file()


FAR = 10**6   # the import distance of a module the targets do not import yet (below a route sorry, parent unproved)

PENDING = pathlib.Path.home() / "upstream-pr" / "upstream-pending.tsv"   # outside the repository: no commit churn


def upstream_pending() -> dict[str, str]:
    """module -> source branch/PR of the source library that proves it (the human, 2026-10-18: do not duplicate
    Orchestra's open PRs). Columns module, source, date; `#` lines are comments. Absent file: nothing is held."""
    out = {}
    try:
        for line in PENDING.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            if len(cols) >= 2:
                out.setdefault(cols[0].strip(), cols[1].strip())
    except OSError:
        pass
    return out


def stage3(imports, dist, waiting: set[str], below: dict[str, dict[str, int]] | None = None):
    """items (kind rank, import distance, module, sorries, kind, route distance) and held (import distance, module, sorries).
    `below`: batch -> {module: distance to the nearest route sorry} (tools/below_route.py; {} or None: route modules only)."""
    repairs = {}
    rp = WORK / "repairs.txt"
    if rp.exists():
        for line in rp.read_text().splitlines():
            if line.strip() and not line.lstrip().startswith("#"):
                repairs.setdefault(line.split()[0], len(repairs))
    # 2026-10-17: only modules on the sorry route of the open batches (local/sorry-route.json, tools/sorry_route.py) are
    # items: a module the targets import but whose sorries no target uses is not work. A module changed after the route
    # was computed stays an item until the next refresh; without a complete route the import closure is used (STATE).
    # The human, 2026-10-18: also the modules below a route sorry (`below`), at their distance to the nearest one.
    import sorry_route
    route = sorry_route.load()
    STATE["route"] = "import closure (no complete sorry route)" if route is None else "sorry route and below it"
    bdist: dict[str, int] = {}
    for mods in (below or {}).values():
        for m, k in mods.items():
            if m not in bdist or k < bdist[m]:
                bdist[m] = k
    keep = set(dist)
    if route is not None:
        keep = route["route"] | sorry_route.changed_in_batches(route, imports) | set(repairs)
        STATE["off_route"] = sorted(m for m in dist if m not in keep and m not in bdist and li.file_of(m).is_file()
                                    and li.sorry_count(li.file_of(m).read_text(errors="ignore")))
    items, held = [], []
    pending = upstream_pending()
    STATE["pending"] = []   # (module, source): held for an open upstream PR, not items (the human, 2026-10-18)
    for m in list(dist) + sorted(m for m in bdist if m not in dist):
        if m not in keep and m not in bdist:
            continue
        p = li.file_of(m)
        if not p.is_file():
            continue
        text = p.read_text(errors="ignore")
        n = li.sorry_count(text)
        if n == 0 and m not in repairs:
            continue
        kind = "repair" if m in repairs else "disputed" if "STATEMENT-DISPUTED" in text else "proof"
        d = dist.get(m, FAR)
        if m in pending and n > 0 and kind != "repair":
            # the human, 2026-10-18: an open Orchestra branch or PR of the source library proves this module; the
            # routine sync brings the proof. Held whether claimed or not; the hold ends when no sorry is left.
            STATE["pending"].append((m, pending[m])); continue
        if m in waiting and not (kind == "repair" and n == 0) and not claimed(m):
            # the human, 2026-10-17 (supersedes the launcher's 2026-10-14 rule that worked such modules anyway): a stage-3
            # item opens only when every node of its dependencies has a Lean statement, so that the prover sees what is
            # available (stmt_deps and proof_deps, the human 2026-10-18). Exempt: a repair of a proved module (no sorry)
            # and an item already claimed.
            held.append((d, m, n)); continue
        items.append((("repair", "disputed", "proof").index(kind), d, m, n, kind, 0 if m in keep else bdist[m]))
    items.sort(key=lambda x: (x[0], repairs[x[2]] if x[4] == "repair" else x[5], x[1], x[2])); held.sort()
    return items, held


def below_route_reach(g):
    """batch -> {module: distance to the nearest route sorry}, from the DAG `g` and the route (tools/below_route.py)"""
    import below_route
    route = below_route.load_route()
    if route is None:
        return {}, None
    return below_route.reach(g, dag_queue, route), route["t"]


def _d(d) -> str:
    return str(d) if d < FAR else "-"


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "summary"
    imports, dist = analyse()
    lib = {m for m in imports if m not in ("Challenge", "TargetsCheck") and m not in li.library_dirs()} if imports else set()
    if cmd == "outside":
        print("\n".join(sorted(lib - set(dist)))); return 0
    s1, s2, waiting, why, below, route_t = [], [], [], collections.Counter(), {}, None
    g = None
    if dag_queue.nodes_dir().is_dir():
        g = dag_queue.Dag(dag_queue.load())
        s1 = g.stage1(); s2, why = g.stage2(); waiting = g.waiting()
        # retirement of ~/weil-newtargets (2026-10-19): the stage-2 dependency waits of tools/nt_stage2.py put the missing
        # prerequisites first (no dispatch restriction; the human, 2026-10-16)
        import nt_stage2
        s2, why = nt_stage2.eligible(g, s2, why)
        if dist:
            below, route_t = below_route_reach(g)
    items3, held = stage3(imports, dist, {m for m, _ in waiting}, below)
    STATE["below"] = {b: sum(1 for x in items3 if x[5] > 0 and x[2] in mods) for b, mods in below.items()}
    # rework (the human, 2026-10-20): the quarantined modules first; whatever depends on one is not an item meanwhile
    import rework
    rw_rows = rework.load()
    rw_open, blocked_n, blocked_m, rw_clusters, rt_prio = [], set(), set(), [], {}
    if rw_rows:
        # the coordinator, 2026-10-20: retire items whose copy collides in a root's environment come first; those roots wait
        rt_prio, rw_held = rework.priority_retire(rw_rows)
        rw_clusters = rework.clusters(rw_rows, rw_held)   # the human, 2026-10-20: one item per cluster (its root), bottom-up
        # a new root not compiled yet waits for `tools/rework.py autorestore` (it may come back by itself)
        rw_clusters = [c for c in rw_clusters if (rw_rows[c["item"]].get("cause") or "").startswith("error:")]
        rw_open = [c["item"] for c in rw_clusters]
        blocked_n, blocked_m, _ = rework.blocked(g, imports, rw_rows)
        nb = (len(s1), len(s2), len(items3))
        s1 = [x for x in s1 if x[1] not in blocked_n]
        s2 = [x for x in s2 if x[2] not in blocked_n]
        items3 = [x for x in items3 if x[2] not in blocked_m and x[2] not in rw_rows]
        STATE["blocked"] = (nb[0] - len(s1), nb[1] - len(s2), nb[2] - len(items3))
    STATE["rework"] = (len(rw_rows), len(rw_open))
    wfor = {}
    for m, c in waiting:
        wfor.setdefault(m, c)
    if cmd == "summary":
        if rw_rows:
            b = STATE.get("blocked", (0, 0, 0))
            print(f"rework: {len(rw_rows)} quarantined modules (tools/rework.py), {len(rw_open)} open; blocked by rework: "
                  f"stage 1 {b[0]}, stage 2 {b[1]}, stage 3 {b[2]} items")
        print(f"stage 1: {len(s1)} nodes to split")
        print(f"stage 2: {len(s2)} nodes to state" + (f"; not open: " + ", ".join(f"{v} {k}" for k, v in why.items()) if why else ""))
        if dist:
            print(f"stage 3: library modules {len(lib)}; needed by the targets {len(dist)}; outside {len(lib - set(dist))}")
            print(f"stage 3: items from the {STATE.get('route', 'import closure')}"
                  + (f"; {len(STATE['off_route'])} sorried modules in the closure are on no target's route nor below a route sorry (not items)" if STATE.get("off_route") else ""))
            print(f"stage 3: {len(items3)} items (" + ", ".join(f"{k} {sum(1 for x in items3 if x[4] == k)}" for k in ("repair", "disputed", "proof"))
                  + f"; on the route {sum(1 for x in items3 if x[5] == 0)}, below a route sorry {sum(1 for x in items3 if x[5] > 0)}"
                  + (": " + ", ".join(f"{b} {n}" for b, n in STATE["below"].items()) if STATE.get("below") else "")
                  + f"); {len(held)} modules waiting for statements of dependencies (not items)"
                  + (f"; {len(STATE['pending'])} modules held for an open upstream PR (~/upstream-pr/upstream-pending.tsv, not items)" if STATE.get("pending") else ""))
            ns = sum(x[3] for x in items3) + sum(x[2] for x in held)   # held modules are not items again since 2026-10-17
            print(f"stage 3: sorries left on the route and below it {ns}, in {len(items3) + len(held)} modules (text count; "
                  "tools/target_types.sh check prints each target's axioms: a target is closed when sorryAx is not among them)")
        else:
            print("stage 3: not open (lean/TargetsCheck.lean imports no target module yet)")
        return 0
    if cmd != "write":
        print(__doc__); return 2
    WORK.mkdir(exist_ok=True)
    def qsorry(m):
        p = rework.ROOT / (rw_rows[m].get("quarantine") or rework.qpath(m))
        try: return li.sorry_count(p.read_text(errors="ignore"))
        except OSError: return ""
    rows = [(m, 3, "-", "", "retire-first", f"unblocks {n} rework roots")
            for m, n in sorted(rt_prio.items(), key=lambda x: (-x[1], x[0]))]
    rows += [(c["item"], 3, "-", sum(qsorry(m) or 0 for m in c["members"]), "rework", f"root; {c.get('waiting', 0)} quarantined importers wait")
             for c in rw_clusters]
    # retire items (the human, 2026-10-20; coord/retire-items.tsv): after the rework items, before every other queue
    rt_rows = rework.retire_rows()                       # open ones: every `after` copy gone
    rt_all = rework.retire_rows(open_only=False)
    rt_items = [m for m in sorted(rt_rows) if m not in blocked_m and m not in rw_rows and m not in rt_prio]
    rt_items.sort(key=lambda m: (int(rt_rows[m]["depth"]) if rt_rows[m]["depth"].isdigit() else 99, m))
    rows += [(m, 3, rt_rows[m]["depth"] or "-", "", "retire", f"consumers {len(rt_rows[m]['consumers'])}") for m in rt_items]
    items3 = [x for x in items3 if x[2] not in rt_all]   # a copy being retired is no proof item
    rows += [(i, 1, d if d < 10**6 else "-", "", dag_queue.audit_state(g.live[i]), "") for d, i in s1]
    rows += [(i, 2, h, "", "target-statement" if pri == 0 else "state", nb) for pri, h, i, nb in s2]
    rows += [(m, 3, _d(d), n, k, "route" if rd == 0 else rd) for _, d, m, n, k, rd in items3]
    if route_t is not None:
        import below_route
        below_route.write_reach(below, route_t)   # the batch tags (tools/tag_batches.py) read what this run selected
    with open(WORK / "queue.tsv", "w") as f:
        f.write("# item\tstage\tdistance (to a target; to Mathlib in stage 2)\tsorry\tkind\tblockers (stage 2: open stage-2 nodes that wait for it through stmt_deps; stage 3: `route`, or the distance to the nearest route sorry)\n")
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    with open(WORK / "queue.md", "w") as f:
        f.write(f"# Work queue\n\n{len(rows)} items; claim with `tools/claim.py next <group> [--stage N]`.\n\n")
        if rw_rows:
            b = STATE.get("blocked", (0, 0, 0))
            f.write(f"## Rework: quarantined by the upstream sync ({len(rw_clusters)} clusters, {len(rw_rows)} modules)\n\n"
                    "Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: "
                    "its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; "
                    "fix the root, then the dependents as far as possible, deliver every module that compiles.\n\n")
            if rw_clusters:
                f.write("| item (root) | modules | other roots | cause of the root |\n|---|---|---|---|\n")
                for c in rw_clusters:
                    f.write(f"| `{c['item']}` | {len(c['members'])} | {', '.join(c['roots'][1:])[:120]} | {rw_rows[c['item']].get('cause', '')[:160]} |\n")
            f.write(f"\nBlocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 "
                    f"{b[0]}, stage 2 {b[1]}, stage 3 {b[2]} items.\n\n")
        f.write(f"## Stage 1: nodes to split ({len(s1)})\n\n")
        if s1:
            f.write("| node | distance to a target | Lean state on the done branch |\n|---|---|---|\n")
            for d, i in s1:
                f.write(f"| `{i}` | {d if d < 10**6 else '-'} | {dag_queue.audit_state(g.live[i])} |\n")
        f.write(f"\n## Stage 2: nodes to state ({len(s2)})\n\n")
        if s2:
            f.write("| node | distance to Mathlib | kind | blockers |\n|---|---|---|---|\n")
            for pri, h, i, nb in s2:
                f.write(f"| `{i}` | {h} | {'target-statement' if pri == 0 else 'state'} | {nb} |\n")
        if why:
            f.write("\nNot open yet: " + ", ".join(f"{v} nodes that {k.replace('waits', 'wait')}" for k, v in why.items()) + ".\n")
        f.write("\n")
        f.write(f"## Stage 3: modules to prove ({len(items3)})\n\n"
                "On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as "
                "every dependency is stated, whatever the depth); route first, then nearest to a route sorry.\n\n")
        if items3:
            f.write("| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |\n|---|---|---|---|---|\n")
            for _, d, m, n, k, rd in items3:
                f.write(f"| `{m}` | {_d(d)} | {n} | {k} | {'route' if rd == 0 else rd} |\n")
        if held:
            f.write(f"\n## Stage 3: waiting for statements of dependencies ({len(held)})\n\n"
                    "Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).\n\n")
            f.write("| module | distance to a target | sorry | waits for (first unstated node) |\n|---|---|---|---|\n")
            for d, m, n in held:
                f.write(f"| `{m}` | {_d(d)} | {n} | `{wfor.get(m, '')}` |\n")
        if STATE.get("pending"):
            f.write(f"\n## Stage 3: held for an open upstream PR ({len(STATE['pending'])})\n\n"
                    "Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, "
                    "the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.\n\n")
            f.write("| module | source |\n|---|---|\n")
            for m, src in sorted(STATE["pending"]):
                f.write(f"| `{m}` | {src} |\n")
    print(f"wrote {len(rows)} items to coord/queue.tsv and coord/queue.md (stage 3: {len(items3)}, waiting {len(held)}; stage 2: {len(s2)}; stage 1: {len(s1)}"
          + (f"; rework {len(rw_open)} open of {len(rw_rows)}, blocked by rework {sum(STATE.get('blocked', (0, 0, 0)))})" if rw_rows else ")"))
    if dag_queue.nodes_dir().is_dir():  # the reverse index of the blueprint references is regenerated with the queue
        import blueprint_refs
        served, on, same = blueprint_refs.index()
        print(f"wrote coord/blueprint-index.tsv: blueprint nodes on the reach with a DAG node from their proof {served} of {on}; new nodes the same as a blueprint node {same}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
