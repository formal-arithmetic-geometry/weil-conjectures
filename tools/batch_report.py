#!/usr/bin/env python3
"""Per-batch workload of the open queues (2026-10-17, batch accounting).
Rows: batch 2-5 x stage 1/2/3, then one `total` row per batch. An item counts for EVERY batch whose target closure
contains it (not only the earliest, which is what the dispatch tag coord/queue-batches.tsv records).
  open      open queue items in this batch's closure (stage 3: modules / their sorries)
  waiting   work this batch is certain to need in that stage that is not in that stage's queue now (2026-10-18, the
            human, 2026-10-18: show the whole remaining work, not only what can be claimed). Counted over the batch's own
            closure W walked as tools/dag_queue.py walks stage 1 (distances_from with cut: not through a finished node,
            not through an `unsplit` node unless keeps_plan), stopping at this batch's assumed nodes (counted as done) and
            at the other batches' targets (own-work rule below), minus the open items of that stage:
              stage 1: nodes of W that are not unfolded (dag_queue.unfolded: not split+reviewed, not a Mathlib leaf, not
                       finished) and not in the stage-1 queue. Every reachable unsplit node is a stage-1 item, so this is
                       only the children kept under a keep_plan return (which the walk enters) and queue lag; the old-plan
                       children of a split returned without keep_plan are not reached (the redo may prune them);
              stage 2: nodes of W that still need a Lean statement (dag_queue.Dag.needs_statement: not stated, i.e. no Lean
                       declaration of their own, not a Mathlib leaf, not assumed, not finished with their declaration
                       upstream), plus the unstated nodes their statements need below a finished node (Dag.stmt_needed,
                       the criterion of Dag.stage2, 2026-10-18); those not in the stage-2 queue (unsplit, unreviewed,
                       waiting for stmt deps or deeper stage 1, keep_plan returns, batch 5 waiting for Statement.lean, ...);
              stage 3: (a) modules on the batch's live sorry route (own route, else `batches`) that are not stage-3
                       queue items: held by the stage-3 gate (dependencies without Lean statements, tools/queue.py) - shown
                       as modules/sorries; plus (b) nodes of W whose Lean is not proved (not dag_queue.finished: neither
                       closed on the done branch, nor closed in live, nor recorded complete; not a Mathlib leaf; not a
                       live module without `sorry`) and whose module is not one of the modules counted in open or (a); a
                       definition node without any Lean declaration is not counted here (stage 2 writes it), one with
                       unproved Lean is. Only below a route sorry (the human, 2026-10-18; stage-3 rule: prove from the
                       targets downward and prune, lower nodes are a plan, not a to-do list): the node lies in the
                       all-deps closure of a node whose Lean declaration is a sorry on the batch's own route (own, else
                       batches; a route sorry is mapped to the nodes recording it in `lean` or in the upstream audit's
                       decls) or of a target whose own declaration is still a sorry, not descending from a finished node
                       -- the live project's tools/below_route.py, the walk tools/queue.py selects the stage-3 items with
                       (the human, 2026-10-18: a node may be proved as soon as every statement it depends on is stated,
                       whatever its depth), so an open item is never waiting. Plan nodes the Lean route bypassed are
                       left out and not reported.
            Unreachable and pruned nodes (below a finished node, behind an unsplit node) are not counted. Nodes that
            future splits will create cannot be counted, so `total` is a lower bound.
  total     per batch: open + waiting over the three stages, in units of nodes (stages 1/2), sorries (stage-3 modules)
            and nodes (stage-3 (b)).
  running   items held by a worker (dispatcher queue-all.tsv state `held by`)
  review    items delivered and waiting for review/landing (state `delivered by`)
Stages 1/2: this project's coord/queue.tsv, closures computed from the DAG as tools/tag_batches.py does (full dependency
closure of coord/new-targets.txt minus batch3/4/5, coord/batch3/4/5-targets.txt).
Stage 3: the live project's coord/queue.tsv and coord/queue-batches-all.tsv (its open batches).
Own work only (the human, 2026-10-18): batch 4's target depends on batch 3's target, so batch 4's count repeated all of
batch 3's remaining work. A batch's count now ignores the targets (main theorems) of every other batch and what only they
need: stages 1/2 walk the closure stopping at another batch's target node, which is neither counted nor descended
through (a node also reached on a path avoiding them still counts); stage 3 uses the live route's "own" key (walks that
stop at every declaration of the other open batches' target modules, tools/sorry_route.py) for the route modules, and
the live local/stage3-reach.json (tools/queue.py write: the modules below each batch's route sorries, by the same walk
as tools/tag_batches.py) for the items below the route, and the tags of coord/queue-batches-all.tsv for a module on no
own route (changed since the route); a batch without an own route falls back to the tags throughout. `excl` is
computed from the same per-batch sets. Reporting only: dispatch, queues, tags and stage gates are unchanged.
Assumptions (coord/assumed.tsv, 2026-10-17): a batch's closure does not enter the nodes it assumes, and the live sorry route
of a batch does not enter the Lean declarations it assumes, so their sorries are not counted for it.
Usage: tools/batch_report.py [--queue-all FILE]   (FILE: copy of ~/weil-launcher-all/queue-all.tsv of the Codex machine;
default: ~/weil-launcher-all/queue-all.tsv if present, else the running/review columns are '-')"""
import collections, importlib.util, json, pathlib, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
LIVE = pathlib.Path("/home/ubuntu/weil-conjectures-sheaf")
import dag_queue as dq
_spec = importlib.util.spec_from_file_location("below_route", LIVE / "tools" / "below_route.py")   # the live walk, with our dag_queue
below_route = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(below_route)
B = ("batch2", "batch3", "batch4", "batch5")
read = lambda f: [l.strip() for l in (R / f).read_text().splitlines() if l.strip() and not l.startswith("#")] if (R / f).exists() else []
b3 = set(read("coord/nodes-batch3-targets.txt")); b4 = set(read("coord/nodes-batch4-targets.txt")); b5 = set(read("coord/nodes-batch5-targets.txt"))
b2 = set(read("coord/new-targets.txt")) - b3 - b4 - b5
g = dq.Dag(dq.load())
import assumed
TG = dict(zip(B, (b2, b3, b4, b5)))
reach = {}
for n, t in TG.items():
    # not entering a batch's assumptions (coord/assumed.tsv), nor the other batches' targets (the human, 2026-10-18);
    # distances_from records a stop node before stopping, so those targets are removed again
    other = set().union(*[v for k, v in TG.items() if k != n]) - t
    reach[n] = set(g.distances_from(t & set(g.live), stop=set(assumed.nodes_for(n)) | other)) - other
def rows(p):
    for l in p.read_text().splitlines():
        r = l.split("\t")
        if not l.startswith("#") and len(r) >= 2: yield r
items = []   # (stage, item, project, batches, weight)
for r in rows(R / "coord/queue.tsv"):
    if r[1] in ("1", "2"): items.append((r[1], r[0], str(R), {b for b in B if r[0] in reach[b]}, 1))
lb = {r[0]: set(r[1].split(",")) & set(B) for r in rows(LIVE / "coord/queue-batches-all.tsv")}
try:   # own routes (2026-10-18): {batchN: set(modules)}; a batch missing here falls back to queue-batches-all.tsv
    _sr = json.loads((LIVE / "local/sorry-route.json").read_text())
    own, own_t = {k: set(v) for k, v in (_sr.get("own") or {}).items() if k in B}, _sr.get("t", 0)
except (OSError, ValueError):
    _sr, own, own_t = {}, {}, 0
try:   # the modules below each batch's route sorries, as tools/queue.py write selected the items (2026-10-18)
    reach3 = {b: set(v) for b, v in json.loads((LIVE / "local/stage3-reach.json").read_text()).get("batches", {}).items()}
except (OSError, ValueError):
    reach3 = {}
def live_batches(m):
    t = lb.get(m, set())
    onown = any(m in v for v in own.values())
    out = set()
    for b in B:
        if b not in own: ok = b in t
        else: ok = m in own[b] or m in reach3.get(b, ()) or (b in t and not onown)   # own route; below its route sorries; a new sorry no own route knows yet
        if ok: out.add(b)
    return out
for r in rows(LIVE / "coord/queue.tsv"):
    if r[1] == "3":
        try: n = int(r[3])
        except (IndexError, ValueError): n = 0
        items.append(("3", r[0], str(LIVE), live_batches(r[0]), max(n, 1)))
qa = pathlib.Path(sys.argv[sys.argv.index("--queue-all") + 1]) if "--queue-all" in sys.argv else pathlib.Path.home() / "weil-launcher-all/queue-all.tsv"
state = {}
if qa.exists():
    for r in rows(qa):
        if len(r) >= 5: state[(r[3].rstrip("/"), r[2])] = r[4]
C = collections.defaultdict(lambda: [0, 0, 0, 0, 0])   # modules, sorries, exclusive, running, review
untagged = collections.Counter()
for stg, it, proj, bs, w in items:
    if not bs: untagged[stg] += 1
    st = state.get((proj, it), "")
    for b in bs:
        c = C[(b, stg)]; c[0] += 1; c[1] += w; c[2] += len(bs) == 1
        c[3] += st.startswith("held by"); c[4] += st.startswith("delivered by")
have = bool(state)
# waiting (the human, 2026-10-18): the batch's certain remaining work that is not in the queue now
q12 = collections.defaultdict(set)
for r in rows(R / "coord/queue.tsv"):
    q12[r[1]].add(r[0])
q3 = {it for stg, it, proj, bs, w in items if stg == "3"}
try:
    _route = json.loads((LIVE / "local/sorry-route.json").read_text()).get("batches") or {}
except (OSError, ValueError):
    _route = {}
def live_file(m): return LIVE / "lean" / (m.replace(".", "/") + ".lean")
W = {}
for n, t in TG.items():
    other = set().union(*[v for k, v in TG.items() if k != n]) - t
    A = set(assumed.nodes_for(n))
    w1 = set(g.distances_from(t & set(g.live), cut=True, stop=A | other)) - other - A
    s1 = {i for i in w1 if not dq.unfolded(g.live[i])} - q12["1"]
    # 2026-10-18: the same criterion as dag_queue.Dag.stage2: a finished node is stated (not counted), and a node below a
    # finished node counts only when the statement of a reached node needs it (stmt_needed)
    s2w = {i for i in w1 if g.needs_statement(i)}
    s2 = (s2w | (g.stmt_needed(s2w) - other - A)) - q12["2"]
    rmods = own.get(n, set(_route.get(n) or ()))
    held = sorted(m for m in rmods - q3 if live_file(m).is_file())
    hs = 0
    for m in held:
        try: hs += max(dq.li.sorry_count(live_file(m).read_text(errors="ignore")), 1)
        except OSError: pass
    counted = rmods | {it for stg, it, proj, bs, w in items if stg == "3" and n in bs}
    # (b) the human, 2026-10-18 (stage-3 rule: prove from the targets downward and prune; lower nodes are a plan, not a
    # to-do list): a node without proved Lean counts only below a route sorry: the live project's tools/below_route.py
    # walk (roots: the nodes whose declarations are sorries on the batch's own route, else batches, the sorried targets
    # among them; through all deps, not descending from a finished node), the one tools/queue.py selects the items with.
    # Not counted: a node whose Lean is proved (finished, or a live module without `sorry`), and a node whose module is an
    # open item or a gate-held route module (counted above). The nodes of the plan outside that walk are left out
    # without being reported.
    def proved(i):
        d = g.live[i]
        if dq.finished(d): return True
        m = dq.module_of(d)
        if not (m and live_file(m).is_file()): return False
        try: return dq.li.sorry_count(live_file(m).read_text(errors="ignore")) == 0
        except OSError: return False
    below = set(below_route.below(g, dq, n, _sr, TG, A)[0]) if _sr else set()
    s3 = set()
    for i in w1 & below:
        d = g.live[i]
        if dq.is_leaf(d) or proved(i): continue
        m = dq.module_of(d)
        if m and m in counted: continue
        if dq.is_def(d) and not dq.has_decl(d): continue
        s3.add(i)
    W[n] = (len(s1), len(s2), len(held), hs, len(s3))
print(f"{'batch':7} {'stage':5} {'open':>15} {'waiting':>26} {'exclusive':>10} {'running':>8} {'review':>7}")
for b in B:
    for stg in "123":
        c = C[(b, stg)]
        o = f"{c[0]} mod/{c[1]} sorry" if stg == "3" else str(c[0])
        wv = W[b]
        wt = f"{wv[2]} mod/{wv[3]} sorry + {wv[4]} nodes" if stg == "3" else str(wv[int(stg) - 1])
        print(f"{b:7} {stg:5} {o:>15} {wt:>26} {c[2]:>10} {(c[3] if have else '-'):>8} {(c[4] if have else '-'):>7}")
    wv = W[b]; o1, o2, o3 = C[(b, "1")][0], C[(b, "2")][0], C[(b, "3")][1]
    tot = o1 + wv[0] + o2 + wv[1] + o3 + wv[3] + wv[4]
    print(f"{b:7} total {tot:>15}   = stage 1 {o1 + wv[0]} + stage 2 {o2 + wv[1]} + stage 3 {o3 + wv[3]} sorries + {wv[4]} nodes")
print("legend: open = claimable queue items now; waiting = certain own work of that stage not in the queue yet (stage 1 not "
      "split, stage 2 no Lean statement, stage 3 gate-held route modules + nodes without proved Lean below a route sorry); total = open + "
      "waiting; own work only, assumed nodes done")
print("future splits cannot be counted, so each total is a lower bound")
print("open items in no batch closure:", dict(untagged) or 0, "| dispatcher state:", qa if have else "not available",
      "| stage 3 own routes:", ",".join(sorted(own)) or "none (queue-batches-all.tsv)")
