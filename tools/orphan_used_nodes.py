#!/usr/bin/env python3
"""Nodes whose Lean declaration other modules use but that no node cites (the human, 2026-10-26: a landed node used by
other modules' declarations had no DAG parent, so the progress walk never reached it; commit 6e6c1b18bfd fixed one).

Report only: it never refuses or changes anything (the human, 2026-10-24: a check informs, it does not block).
A node is listed when
  - it records a declaration (lean.declaration / lean.declarations) in a library module that exists in live,
  - no live node lists it in stmt_deps, proof_deps or the `uses` of a proof step (it is not a batch target either),
  - another library module that imports its module (transitively) names that declaration in its code (comments
    removed): the full name, a suffix of at least two components, or the last component when it is at least 12
    characters long (a namespace opened by `open`/`namespace`).
Each hit says which modules use it and the nodes recorded in those modules (the likely parents).

    python3 tools/orphan_used_nodes.py [--hours N] [--json]   N: only nodes whose node file changed in the last N hours
"""
import collections, json, os, pathlib, re, subprocess, sys

R = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R / "tools"))
import dag_queue as dq, leanindex as li  # noqa: E402

IDENT = re.compile(r"[A-Za-z_À-ɏͰ-Ͽ][\w.'!?À-ɏͰ-Ͽ₀-ₜ]*")


def node_decls(d):
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    return ([l["declaration"]] if l.get("declaration") else []) + list(l.get("declarations") or [])


def names(decl):
    p = decl.split(".")
    out = {".".join(p[k:]) for k in range(len(p) - 1)}   # the full name and every suffix of >= 2 components
    if len(p[-1]) >= 12:
        out.add(p[-1])
    return out


def changed_nodes(hours):
    r = subprocess.run(["git", "log", f"--since={hours} hours ago", "--name-only", "--format=", "--", "dag/nodes"],
                       cwd=R, capture_output=True, text=True).stdout
    return {pathlib.Path(x).stem for x in r.split() if x.endswith(".json")}


def find(hours=None):
    g = dq.Dag(dq.load()); live = g.live
    cited = {c for j in live for c in g.deps(j, "all")}
    import progress_reach
    tg = set().union(*progress_reach.targets().values())
    recent = changed_nodes(hours) if hours else None
    cand = {}   # node -> (module, decls)
    for i, d in live.items():
        if i in cited or i in tg or dq.is_leaf(d) or progress_reach.convention(d) or progress_reach.mathlib(d):
            continue
        if recent is not None and i not in recent:
            continue
        m, ds = dq.module_of(d), node_decls(d)
        if m and ds and li.file_of(m).is_file():
            cand[i] = (m, ds)
    want = collections.defaultdict(set)   # name as written -> nodes
    for i, (m, ds) in cand.items():
        for x in ds:
            for n in names(x):
                want[n].add(i)
    _, imports = li.scan()
    bymod = collections.defaultdict(list)
    for i, d in live.items():
        m = dq.module_of(d)
        if m: bymod[m].append(i)
    memo, hits = {}, collections.defaultdict(set)
    for p in li.library_files():
        try:
            text = p.read_text(errors="ignore")
        except OSError:
            continue
        found = {t for t in IDENT.findall(text) if t in want}
        if not found:
            continue
        u = li.module_of(p)
        up = li.closure(u, imports, memo)
        pairs = [(t, i) for t in found for i in want[t] if cand[i][0] != u and cand[i][0] in up]
        if not pairs:
            continue
        code = set(IDENT.findall(li.strip(text)))   # the lexer is slow: only for files with a candidate use
        for t, i in pairs:
            if t in code:
                hits[i].add(u)
    out = []
    for i in sorted(hits):
        users = sorted(hits[i])
        parents = sorted({j for u in users for j in bymod.get(u, ()) if j != i})
        out.append({"node": i, "module": cand[i][0], "used_in": users, "nodes_of_users": parents})
    return out, len(cand)


def main():
    hours = None
    if "--hours" in sys.argv:
        hours = float(sys.argv[sys.argv.index("--hours") + 1])
    out, n = find(hours)
    if "--json" in sys.argv:   # recent_24h: the orphans whose node file changed in the last 24 h (hourly report)
        rc = changed_nodes(24)
        print(json.dumps({"checked": n, "orphans": out, "recent_24h": [r["node"] for r in out if r["node"] in rc]})); return 0
    print(f"{len(out)} node(s) used by other modules but cited by no node (of {n} uncited nodes with a live declaration"
          + (f", changed in the last {hours:g} h" if hours else "") + ")")
    for r in out:
        print(f"  {r['node']} ({r['module']}): used in {', '.join(r['used_in'][:3])}"
              + (f" +{len(r['used_in']) - 3}" if len(r["used_in"]) > 3 else "")
              + (f"; nodes there: {', '.join(r['nodes_of_users'][:3])}" if r["nodes_of_users"] else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
