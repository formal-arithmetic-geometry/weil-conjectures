"""Incremental tools/check_dag.py for one stage-1 delivery (pfinc, 2026-10-17: the server preflight ran the full check,
~20-40 s of one core, for ~1700 deliveries an hour).

    delivery_findings(base, ids) -> (bad, routes) | None

The full check of the delivery tree is compared with the cached full check of the base (dag_delta.check_ref) and only
the lines that differ count (dag_delta.delivery_findings). A delivery changes a handful of node files (the item, its new
nodes) and the realized fields of unit records, so here only the lines that can differ are recomputed on the delivery
tree, and every other line is taken from the base text:
  deps, units (node), route   for the changed nodes and the nodes citing them (stmt, proof, step uses, merged);
  units (realized), cycles, targets   on the whole delivery graph (each one pass over it).
None (the caller runs the full check) whenever the delivery does anything else: a file deleted or renamed, a change
outside dag/nodes, dag/units and coord/reports, a unit record changed beyond `realized`/`realized_by`, a changed node
merged, an unparsable file or duplicate id, ids findings or unclassified finding lines in the base text, or SHEAF_DAG
not naming this tree's dag/nodes.
"""
from __future__ import annotations
import collections, json, pathlib, re, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dag_queue as dq  # noqa: E402
import dag_delta  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODE_LINE = re.compile(r"^units: (\S+) (has no chapter \(|names a unit that does not exist: )")


def _git(*a):
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    return r.stdout


def _none(why):
    """the full check is needed; SHEAF_INC_DEBUG=1 says why on stderr"""
    import os
    if os.environ.get("SHEAF_INC_DEBUG") == "1":
        sys.stderr.write(f"dag_inc: full check: {why}\n")


def _owner(line):
    """('node'|'unit'|'global'|None, id) of a base line in a category recomputed here"""
    if line.startswith("deps: ") or line.startswith("route: "):
        return "node", line.split(" ", 2)[1]
    if line.startswith("units: "):
        m = NODE_LINE.match(line)
        return ("node", m.group(1)) if m else ("unit", line.split(" ", 2)[1])
    if line.startswith(("cycles:", "targets:")):
        return "global", None
    return None, None


def delivery_findings(base, ids):
    if dq.nodes_dir().resolve() != (ROOT / "dag" / "nodes").resolve():
        return _none("SHEAF_DAG elsewhere")
    base_text = dag_delta.check_ref(base)
    for line in base_text.splitlines():
        if line.startswith("ids:"):
            return _none("ids line in base")
        if line in dag_delta.findings(line, ()) or "ERROR" in line:
            if _owner(line)[0] is None:
                return _none("unclassified finding line in base")
    # the changed files
    changed_nodes, changed_units = [], []
    for row in _git("diff", "--no-renames", "--name-status", base, "HEAD").splitlines():
        st, path = row.split("\t", 1)
        if path.startswith("coord/reports/"):
            continue
        if st not in ("M", "A") or not path.endswith(".json"):
            return _none("deleted/renamed/non-json change")
        if path.startswith("dag/nodes/"):
            changed_nodes.append((st, path))
        elif path.startswith("dag/units/") and path.count("/") == 2:
            if st != "M":
                return _none("unit record added")
            changed_units.append(path)
        else:
            return _none("change outside dag/nodes, dag/units, reports")
    for path in changed_units:
        old, new = json.loads(_git("show", f"{base}:{path}")), json.loads((ROOT / path).read_text())
        for d in (old, new):
            d.pop("realized", None); d.pop("realized_by", None)
        if old != new:
            return _none("unit record changed beyond realized")

    # the delivery tree, parsed once
    nodes, seen = {}, set()
    for p in sorted(dq.nodes_dir().rglob("*.json")):
        try:
            d = json.loads(p.read_text())
        except (OSError, json.JSONDecodeError):
            return _none("unparsable file")
        i = dq.field(d, "id") if isinstance(d, dict) else None
        if not i or str(i) in seen:
            return _none("no id or duplicate id")
        seen.add(str(i)); nodes[str(i)] = d
    C = set()
    for st, path in changed_nodes:
        d = json.loads((ROOT / path).read_text())
        i = str(dq.field(d, "id"))
        if dq.field(d, "merged") or str(dq.field(d, "status") or "").lower() == "merged":
            return _none("changed node merged")
        if st == "M":
            o = json.loads(_git("show", f"{base}:{path}"))
            if str(dq.field(o, "id")) != i or dq.field(o, "merged") or str(dq.field(o, "status") or "").lower() == "merged":
                return _none("id changed or merged on base")
        C.add(i)
    g = dq.Dag(nodes)
    import units as un
    units, chapters = un.load_units()

    rev = collections.defaultdict(set)
    for j, d in nodes.items():
        for c in dq.deps_of(d, "all"):
            rev[c].add(j)
        m = dq.field(d, "merged")
        if m:
            rev[str(m)].add(j)
    S = set(C)
    for c in C:
        S |= rev.get(c, set())

    errors = []
    # deps (check_dag.main), for S
    for i in sorted(S):
        d = nodes.get(i)
        if d is None:
            continue
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
    # cycles, targets (check_dag.main), whole graph
    import check_dag as cd
    graph = {i: [c for c in dict.fromkeys(dq.deps_of(d, "all")) if c in g.live] for i, d in g.live.items()}
    for i in sorted(i for i, cs in graph.items() if i in cs):
        errors.append(f"cycles: {i} depends on itself")
    for c in sorted((c for c in cd.sccs(graph) if len(c) > 1), key=lambda c: (-len(c), sorted(c)[0])):
        errors.append(f"cycles: {len(c)} nodes depend on each other: " + ", ".join(sorted(c)))   # --cycles: all members
    if not g.targets:
        errors.append("targets: no node is a target")
    # units, node part (units.check), for S
    for i in sorted(S):
        d = g.live.get(i)
        if d is None:
            continue
        if d.get("chapter") not in chapters:
            errors.append(f"units: {i} has no chapter ({d.get('chapter')!r})")
        if d.get("unit") is not None and d.get("unit") not in units:
            errors.append(f"units: {i} names a unit that does not exist: {d.get('unit')!r}")
    # units, realized part (units.check): all units (one pass over the graph, tools/units.py unit_bits)
    _dall = {}

    def deps_all(x):
        r = _dall.get(x)
        if r is None:
            r = _dall[x] = g.deps(x, "all")
        return r
    full_carriers = []
    for v, vrec in units.items():
        vr = vrec.get("realized") or {}
        statements, steps = vr.get("statement") or [], vr.get("steps") or []
        if not statements or len(steps) != len(vrec.get("steps") or []) or not all(steps):
            continue
        full_carriers.append((v, set(statements + [x for step in steps for x in step])))
    errors += un.realized_errors(nodes, g, units, deps_all, full_carriers)
    U = set(units)
    # route (units.check), for S
    for i in sorted(S):
        d = g.live.get(i)
        if d is None:
            continue
        u = d.get("unit")
        if not u or dq.is_def(d) or u not in units:
            continue
        if not units[u].get("uses") and not units[u].get("steps"):
            continue
        allowed = un.closure(units, u)
        for c in g.deps(i, "proof"):
            if c not in g.live or dq.is_def(nodes[c]) or dq.is_leaf(nodes[c]) or dq.finished(nodes[c]):
                continue
            cu, cc = nodes[c].get("unit"), nodes[c].get("chapter")
            if not (cu in allowed if cu else True):
                if c in (d.get("tool_uses") or []):
                    continue
                if str(d.get("status")) in ("split", "mathlib") and d.get("reviewed"):
                    errors.append(f"route: {i} ({u}) depends on {c} ({cu or cc}), outside its unit's route")

    kept = []
    for line in base_text.splitlines():
        kind, who = _owner(line)
        if kind == "global" or (kind == "node" and who in S) or (kind == "unit" and who in U):
            continue
        kept.append(line)
    current = "\n".join(kept + errors) + "\n"
    return dag_delta.delivery_findings(current, base_text, ids)
