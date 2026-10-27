#!/usr/bin/env python3
"""Progress of each batch target (the human, 2026-10-22): the target node's downstream dependency nodes, how many are
done and how many are not, counting only work that is really needed.

Walk from the batch's target nodes (coord/nodes-batchN-targets.txt; batch 2: coord/new-targets.txt minus the others)
over stmt_deps and proof_deps:
  - a node another batch targets is not entered (that batch's own work);
  - a convention node (lean.convention) and a Mathlib leaf need no work: not counted at all;
  - an assumed node (coord/assumed.tsv) counts as done and is not entered;
  - a proved node counts as done and is not entered: what lies below it is pruned (the proof did not need it or it is
    done): dag_queue.finished, or its recorded module is in live without `sorry`; also when its declaration rests on a
    `sorry` below (that sorry is another node's work, counted there through the sorry route);
  - an unsplit node is open (stage 1) and is not entered, unless it keeps its plan: its listed dependencies are an old
    plan the split may prune (the rule of tools/dag_queue.py);
  - every other node is open and entered: stage 2 when it has no Lean statement, rework when its module is quarantined
    or missing, stage 3 when its module still has `sorry`.
A dependency of an open node that the eventual proof will not use cannot be known before it is written: such a node is
counted (it is the plan). The total ("nodes below the targets", 2026-10-27) is the open nodes plus every done node of the
route, the walk continued THROUGH done nodes (tools/progress_reach.py route_totals): split children and proof
dependencies of finished nodes stay counted; bypassed plan nodes, conventions and Mathlib leaves do not. Upstream sorried declarations with no node (dag/lean_audit.json) in a batch's import closure
are listed separately: they are work the DAG does not see yet.

    python3 tools/target_progress.py [--json]
"""
import collections, json, os, re, sys, pathlib
R = pathlib.Path(__file__).resolve().parent.parent
os.chdir(R); sys.path.insert(0, str(R / "tools"))
import dag_queue as dq, leanindex as li, assumed

import progress_reach as pr
ids = pr.ids
T = pr.targets()
live = dq.load(); g = dq.Dag(live)
from own_decl import sorries
CLS, route_nonode = pr.classify(g, T, report=True)   # 2026-10-26: report mode (split-since-route bridge, blocked by rework)
_ROUTE = pr.ROUTE
# 2026-10-27 (the human): the total of a route is its open nodes plus every done node of the route, reached through done
# nodes too (progress_reach.route_totals); the walk's own count stopped below written proofs and quarantined modules and
# shrank as work got done
RT = pr.route_totals(g, CLS, T)
out = {}
for b in sorted(T):
    cls = CLS[b]
    c = collections.Counter(cls.values())
    rdone = RT[b][1]
    c["done"] = sum(1 for i in rdone if cls.get(i) != "assumed"); c["assumed"] = sum(1 for i in rdone if cls.get(i) == "assumed")
    up = sum(1 for i in rdone if str(dq.module_of(live[i]) or "").startswith("WeilConjectures."))
    mods3 = {dq.module_of(live[i]) for i, k in cls.items() if k.startswith("stage 3")}
    out[f"batch{b}"] = {"route": _ROUTE.get(b), "route_decls_without_node": len(route_nonode[b]), "counted": len(RT[b][0]) + len(rdone),
                        "walk_counted": len(cls), "done_in_upstream_modules": up, **dict(c), "stage3_modules": len(mods3),
                        "stage3_sorries": sum(1 for i, k in cls.items() if k.startswith("stage 3"))}
# upstream sorries without a node, per batch import closure
_, imp = li.scan()
def clo(ts):
    s = set(ts); q = collections.deque(ts)
    while q:
        x = q.popleft()
        for y in imp.get(x, ()):
            if y not in s: s.add(y); q.append(y)
    return s
try:
    la = json.load(open("dag/lean_audit.json"))["branches"]["slopmaster2"]["sorries"]
    nonode = [x for x in la if not x.get("nodes")]
except Exception:
    nonode = []
for b in sorted(T):
    C = clo(ids(f"coord/batch{b}-targets.txt"))
    A = set(assumed.decls_for(f"batch{b}")) if hasattr(assumed, "decls_for") else set()
    out[f"batch{b}"]["upstream_sorries_without_node"] = sum(1 for x in nonode if x["module"] in C and x["name"] not in A)
if "--json" in sys.argv:
    print(json.dumps(out, indent=1)); sys.exit(0)
for b, r in out.items():
    open_ = sum(v for k, v in r.items() if k.startswith(("stage", "rework", "open:")) and isinstance(v, int) and k not in ("stage3_modules", "stage3_sorries"))
    done = r.get("done", 0) + r.get("assumed", 0)
    print(f"{b}: {r['counted']} nodes below the targets; done {done} ({100*done/max(r['counted'],1):.0f}%, of which assumed {r.get('assumed',0)}, "
          f"in upstream WeilConjectures.* modules {r['done_in_upstream_modules']}); open {open_}")
    for k in ("stage 1 (unsplit)", "stage 2 (no Lean statement)", "stage 3 (Lean has sorry)", "stage 3 (split since route)", "stage 3 (blocked by rework)", "open: proved here, rests on sorry below", "rework (module quarantined/missing)"):
        print(f"    {k}: {r.get(k, 0)}" + (f"  [in {r['stage3_modules']} modules]" if k == "stage 3 (Lean has sorry)" else ""))
    print(f"    route sorries with no node: {r['route_decls_without_node']}   (route: {r['route'] or 'NOT COMPUTED - stage 3 below written proofs unknown'})")
    print(f"    upstream sorries in the import closure with no node yet: {r['upstream_sorries_without_node']}")
