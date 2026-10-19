#!/usr/bin/env python3
"""Stage-3 work below the sorry route (the human, 2026-10-18: a node may be proved as soon as every statement it depends
on, stmt_deps and proof_deps, has a Lean statement, whatever its depth below the target).

For each open batch N (coord/batchN-targets.txt without coord/batchN-complete.txt) the ROOTS are the DAG nodes whose
Lean declarations (the `lean` record's declaration/declarations, or the upstream audit's decls) are sorried declarations
on the batch's own route (local/sorry-route.json "own", else "batches"; tools/sorry_route.py); a target whose own
declaration is still a sorry is one of them. The roots are walked through every dependency (stmt and proof), not
entering the nodes the batch assumes (coord/assumed.tsv), nor the other open batches' target nodes, and not descending
from a finished node (closed on the done branch, dag_queue.finished); the walk is intersected with the batch's own reach
(its target nodes walked the same way, cut at finished nodes), as tools/batch_report.py of the new-targets project walks
its stage-3 (b). Every node of that set is "below a route sorry" of the batch, at the distance of the fewest dependency
steps from a root (0 for a root); a module is below a route sorry at the distance of its nearest node. Stated nodes
whose Lean the route does not reach yet are therefore work as soon as their module is in live with a `sorry` (the
parent's proof is not written, so the Lean walk cannot see them); nodes in no root's closure are bypassed by the Lean
route and are not work. The walk does not descend from a node whose Lean is proved either: finished, or a live module
without `sorry` (stage-3 rule: prove from the targets downward and prune; what a proved module uses is settled by its
proof, and the plan below it is not work until the route reaches it) -- the stop of batch_report's stage-3 (b), except
that a sorried live module is descended from (its proof is not written, so its plan still stands).

The batches' target NODES are read from the new-targets project (NEWTARGETS/coord/batchN-targets.txt; the open batch
without such a file, batch 2, is the rest of that project's SHEAF_TARGET_LIST), because the live coord/batchN-targets.txt
list the Lean target modules. Shared by tools/queue.py (the items and local/stage3-reach.json), tools/tag_batches.py
(the batch tags) and the new-targets project's tools/batch_report.py (loaded by path, with that project's dag_queue):
the three agree by construction. Pure functions over an in-memory DAG: `g` is a dag_queue.Dag, `dq` the dag_queue
module that built it.

Usage: tools/below_route.py            print, per open batch, the roots and the modules below a route sorry by distance
"""
from __future__ import annotations
import collections, json, os, pathlib, re, sys

R = pathlib.Path(__file__).resolve().parent.parent
NEWTARGETS = pathlib.Path(os.environ.get("SHEAF_NEWTARGETS") or R)   # 2026-10-19: one repository (~/weil-newtargets retired)
REACH = R / "local" / "stage3-reach.json"


def _lines(p: pathlib.Path) -> list[str]:
    try:
        return [l.split()[0] for l in p.read_text().splitlines() if l.strip() and not l.lstrip().startswith("#")]
    except OSError:
        return []


def open_batches(root: pathlib.Path = R) -> list[str]:
    """the open batches of the live project, 'batchN', in order"""
    ns = sorted(int(m.group(1)) for p in (root / "coord").glob("batch*-targets.txt")
                if (m := re.fullmatch(r"batch(\d+)-targets\.txt", p.name)))
    return [f"batch{n}" for n in ns if not (root / f"coord/batch{n}-complete.txt").exists()]


def batch_nodes(batches=None, newtargets: pathlib.Path = NEWTARGETS) -> dict[str, set[str]]:
    """batch -> its target nodes: NEWTARGETS/coord/batchN-targets.txt; the one batch without a file gets the rest of
    NEWTARGETS's target list (coord/sheaf.env SHEAF_TARGET_LIST, default coord/new-targets.txt)."""
    batches = list(batches) if batches is not None else open_batches()
    out, missing = {}, []
    for b in batches:
        nodes = set(_lines(newtargets / "coord" / f"nodes-{b}-targets.txt"))   # node ids; coord/batchN-targets.txt are modules
        if nodes:
            out[b] = nodes
        else:
            missing.append(b)
    if missing:
        tl = "coord/new-targets.txt"
        try:
            for line in (newtargets / "coord" / "sheaf.env").read_text().splitlines():
                line = line.split("#", 1)[0].strip()
                if line.startswith("SHEAF_TARGET_LIST="):
                    tl = line.split("=", 1)[1].strip().strip("'\"") or tl
        except OSError:
            pass
        rest = set(_lines(newtargets / tl)) - set().union(*out.values()) if out else set(_lines(newtargets / tl))
        out[missing[0]] = rest
        for b in missing[1:]:
            out[b] = set()
    return out


def load_route(root: pathlib.Path = R):
    """local/sorry-route.json as written by tools/sorry_route.py, or None when missing, unreadable or not `ok`"""
    try:
        d = json.loads((root / "local" / "sorry-route.json").read_text())
    except (OSError, ValueError):
        return None
    if not d.get("ok") or "batches" not in d:
        return None
    return d


def route_of(route: dict, batch: str) -> dict[str, list[str]]:
    """{module: [sorried declarations]} of the batch's own route, else its plain route"""
    own = route.get("own") or {}
    return own.get(batch) or route.get("batches", {}).get(batch) or {}


def decl_names(d: dict, done_branch: str) -> list[str]:
    """the Lean declarations a node records: its `lean` record (declaration, declarations) and the upstream audit's decls"""
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    out = ([l.get("declaration")] if l.get("declaration") else []) + [x for x in l.get("declarations") or [] if isinstance(x, str)]
    return out + [x["name"] for x in ((d.get("lean_audit") or {}).get(done_branch) or {}).get("decls") or []
                  if isinstance(x, dict) and x.get("name")]


def below(g, dq, batch: str, route: dict, targets_of: dict[str, set[str]], assumed_nodes: set[str]) -> tuple[dict[str, int], set[str]]:
    """(node -> fewest dependency steps from a root, roots) for `batch`: the nodes below a route sorry of the batch that
    the batch's own targets reach (see the module docstring)."""
    t = targets_of.get(batch, set()) & set(g.live)
    other = set().union(*[v for k, v in targets_of.items() if k != batch]) - t if targets_of else set()
    A = set(assumed_nodes)
    w1 = set(g.distances_from(t, cut=True, stop=A | other)) - other - A
    rdecls = {x for ds in route_of(route, batch).values() for x in ds}
    db = dq.done_branch()
    roots = {i for i, d in g.live.items() if any(x in rdecls for x in decl_names(d, db))}
    dist: dict[str, int] = {}
    q = collections.deque((r, 0) for r in sorted(roots) if r not in A and r not in other)
    while q:
        i, k = q.popleft()
        if i in dist:
            continue
        dist[i] = k
        if i not in roots and proved(g.live[i], dq):
            continue
        for c in g.deps(i, "all"):
            if c in g.live and c not in dist and c not in A and c not in other:
                q.append((c, k + 1))
    return {i: k for i, k in dist.items() if i in w1}, roots


_SORRIES: dict[str, int] = {}


def sorries(module: str, dq, root: pathlib.Path = R) -> int:
    """the `sorry`/`admit` count of the live module's text, -1 when the module is not in live"""
    if module not in _SORRIES:
        p = root / "lean" / (module.replace(".", "/") + ".lean")
        try:
            _SORRIES[module] = dq.li.sorry_count(p.read_text(errors="ignore")) if p.is_file() else -1
        except OSError:
            _SORRIES[module] = -1
    return _SORRIES[module]


def proved(d: dict, dq) -> bool:
    """the node's Lean is proved: finished (dag_queue), or its recorded module is in live without `sorry`"""
    if dq.finished(d):
        return True
    m = dq.module_of(d)
    return bool(m) and sorries(m, dq) == 0


def modules_of(g, dq, nodes: dict[str, int]) -> dict[str, int]:
    """module -> the distance of its nearest node (nodes with a recorded module only)"""
    out: dict[str, int] = {}
    for i, k in nodes.items():
        m = dq.module_of(g.live[i])
        if m and (m not in out or k < out[m]):
            out[m] = k
    return out


def reach(g, dq, route: dict | None = None, root: pathlib.Path = R) -> dict[str, dict[str, int]]:
    """batch -> {module: distance} for every open batch of the live project; {} without a complete route"""
    route = route if route is not None else load_route(root)
    if route is None:
        return {}
    import assumed
    tg = batch_nodes(open_batches(root))
    out = {}
    for b in tg:
        nodes, _ = below(g, dq, b, route, tg, assumed.nodes_for(b))
        out[b] = modules_of(g, dq, nodes)
    return out


def write_reach(data: dict[str, dict[str, int]], t: float, path: pathlib.Path = REACH) -> None:
    """local/stage3-reach.json: what tools/queue.py write computed, for tools/tag_batches.py (t = the route's `t`)"""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name("." + path.name)
    tmp.write_text(json.dumps({"t": t, "batches": {b: dict(sorted(v.items())) for b, v in sorted(data.items())}}, indent=0))
    tmp.replace(path)


def read_reach(t: float | None = None, path: pathlib.Path = REACH) -> dict[str, dict[str, int]] | None:
    """the reach tools/queue.py wrote, or None when missing or written for another route (`t` differs)"""
    try:
        d = json.loads(path.read_text())
    except (OSError, ValueError):
        return None
    if t is not None and d.get("t") != t:
        return None
    return {b: dict(v) for b, v in d.get("batches", {}).items()}


def main() -> int:
    sys.path.insert(0, str(R / "tools"))
    import dag_queue as dq
    route = load_route()
    if route is None:
        print("no complete sorry route (local/sorry-route.json)"); return 1
    g = dq.Dag(dq.load())
    import assumed
    tg = batch_nodes(open_batches())
    for b, t in tg.items():
        nodes, roots = below(g, dq, b, route, tg, assumed.nodes_for(b))
        mods = modules_of(g, dq, nodes)
        print(f"{b}: targets {len(t)}, roots {len(roots)}, nodes below a route sorry {len(nodes)}, modules {len(mods)}")
        for m, k in sorted(mods.items(), key=lambda x: (x[1], x[0])):
            print(f"  {k}\t{m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
