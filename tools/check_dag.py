#!/usr/bin/env python3
"""Check the DAG in dag/nodes/ against stages/1-dag.md §6. Reads the nodes as dag_queue.py does (its FIELDS table).

Usage:
  tools/check_dag.py            print what is wrong; exit 1 if anything is
  tools/check_dag.py --cycles   also print every member of every cycle

Checked:
  ids        every node file parses, has an id, and no id occurs in two files;
  deps       every statement dependency, proof dependency and step `uses` names an existing node that is not
             merged; a step uses only nodes listed in `proof_deps`; `merged_into` names a live node;
  cycles     the graph of statement and proof dependencies is acyclic; each strongly connected component with
             more than one node, and each self-loop, is reported and nothing is changed;
  targets    there is at least one target;
  units      the checks of tools/units.py: every node has a chapter and a unit that exist; a unit whose `realized` fields are
             filled has a node for its statement and every step and reaches the units it cites;
  route      a split and reviewed statement whose proof uses a statement of a unit its unit does not cite (stages/1-dag.md §7);
  reach      a node is reached from a target, or from a former target (`target_former`, kept so that the subtree of an
             earlier target is not reported when the target changes), or carries `unreachable` in `import_flags`, never both;
  blueprint  every node carries the `blueprint` field (is, from, same_as) of stages/1-dag.md §6, well formed: `is` is the
             node's own id exactly for a node imported from the blueprint, `from` names a blueprint node and a place,
             `same_as` lists blueprint nodes (tools/blueprint_refs.py; new nodes and split items are checked strictly by
             tools/review_split.py and tools/preflight_delivery.py).
"""
from __future__ import annotations
import collections, json, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dag_queue as dq  # noqa: E402


def sccs(graph: dict[str, list[str]]) -> list[list[str]]:
    """Tarjan, without recursion."""
    index, low, on, stack, out, n = {}, {}, set(), [], [], 0
    for root in graph:
        if root in index:
            continue
        work = [(root, iter(graph[root]))]
        index[root] = low[root] = n; n += 1; stack.append(root); on.add(root)
        while work:
            v, it = work[-1]
            for w in it:
                if w not in graph:
                    continue
                if w not in index:
                    index[w] = low[w] = n; n += 1; stack.append(w); on.add(w)
                    work.append((w, iter(graph[w]))); break
                if w in on:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop(); on.discard(w); comp.append(w)
                        if w == v:
                            break
                    out.append(comp)
    return out


def main() -> int:
    show = "--cycles" in sys.argv
    errors: list[str] = []
    seen: dict[str, pathlib.Path] = {}
    files = sorted(dq.nodes_dir().rglob("*.json"))
    for p in files:
        try:
            d = json.loads(p.read_text())
        except (OSError, json.JSONDecodeError) as e:
            errors.append(f"ids: {p} does not parse: {e}"); continue
        i = dq.field(d, "id") if isinstance(d, dict) else None
        if not i:
            errors.append(f"ids: {p} has no id"); continue
        if str(i) in seen:
            errors.append(f"ids: {i} occurs in {seen[str(i)]} and {p}")
        seen[str(i)] = p
    nodes = dq.load()
    g = dq.Dag(nodes)

    for i, d in nodes.items():
        m = dq.field(d, "merged")
        if i in g.merged:
            if not m or str(m) not in g.live:
                errors.append(f"deps: {i} is merged into {m!r}, which is not a live node")
            continue
        pd = set(str(x) for x in (dq.field(d, "proof_deps") or []))
        for which in ("stmt", "proof"):
            for c in dq.deps_of(d, which):
                if c not in nodes:
                    errors.append(f"deps: {i} ({which}) -> {c}: no such node")
                elif c in g.merged:
                    errors.append(f"deps: {i} ({which}) -> {c}: merged into {g.merged[c]}")
        pf = dq.field(d, "proof")
        if isinstance(pf, list):
            for k, step in enumerate(pf):
                if isinstance(step, dict):
                    for u in step.get("uses") or []:
                        if str(u) not in pd:
                            errors.append(f"deps: {i} step {k + 1} uses {u}, which is not in proof_deps")

    graph = {i: [c for c in dict.fromkeys(dq.deps_of(d, "all")) if c in g.live] for i, d in g.live.items()}
    loops = sorted(i for i, cs in graph.items() if i in cs)
    comps = sorted((c for c in sccs(graph) if len(c) > 1), key=lambda c: (-len(c), sorted(c)[0]))
    for i in loops:
        errors.append(f"cycles: {i} depends on itself")
    for c in comps:
        members = sorted(c)
        errors.append(f"cycles: {len(c)} nodes depend on each other: " + (", ".join(members) if show or len(c) <= 6 else ", ".join(members[:6]) + ", …"))
        if show:
            inside = set(c)
            for a in members:
                for b in graph[a]:
                    if b in inside:
                        kind = "stmt" if b in dq.deps_of(g.live[a], "stmt") else "proof"
                        print(f"  edge\t{a}\t{b}\t{kind}")

    if not g.targets:
        errors.append("targets: no node is a target")
    former = [i for i, d in g.live.items() if d.get("target_former")]
    reach_all = dq.Dag.distances_from(g, g.targets + former)
    for i, d in g.live.items():
        flagged = "unreachable" in (d.get("import_flags") or [])
        if i not in reach_all and not flagged:
            errors.append(f"reach: {i} is not reached from a target and is not flagged unreachable")
        if i in reach_all and flagged:
            errors.append(f"reach: {i} is flagged unreachable but a target reaches it")

    import units as un  # noqa: E402
    errors += un.check(nodes, verbose=False)
    import blueprint_refs as br  # noqa: E402
    errors += br.errors(br.load()[0])
    kinds = collections.Counter(e.split(":")[0] for e in errors)
    for e in errors:
        print(e)
    print(f"{len(files)} files, {len(nodes)} nodes, {len(g.merged)} merged, {len(g.targets)} targets, "
          f"{len(g.dist)} reached, {len(g.live) - len(g.dist)} not reached; "
          f"{len(comps)} cycles ({sum(len(c) for c in comps)} nodes), {len(loops)} self-loops; "
          + ("no errors" if not errors else ", ".join(f"{v} {k}" for k, v in sorted(kinds.items()))))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
