"""The progress walk (the human, 2026-10-22/24): per batch, the nodes below the targets that are really needed, each
classified done or open. tools/target_progress.py reports it; tools/dag_queue.py offers stage-1/2 work only inside it
(2026-10-25, the human: the queue offered ~3300 pruned plan nodes below written proofs as stage-2 items).

The walk starts at the nodes recording a sorried declaration on the batch's sorry route (tools/sorry_route.py) and at
the target nodes; below a node whose own proof is written (tools/own_decl.py) the DAG plan is not followed.

Report mode (classify(g, report=True): tools/target_progress.py, ~/cc1/hourly_health.py; the human, 2026-10-26):
  - a bridge symmetric to the queue's: a module new since the sorry route's commit (split_since_route: the modules
    tools/queue.py stage3() keeps as `changed` and that did not exist at the route's commit) is on no route until the
    next refresh, so its nodes with a DAG parent in this batch's walk (done or not) start the walk too; an open one is
    "stage 3 (split since route)". Once the route is refreshed those modules existed at its commit: the bridge is empty;
  - "stage 3 (blocked by rework)": a stage-3 node whose module tools/rework.py blocked() keeps out of the queue.
The default walk (report=False) is the one tools/queue.py, tools/tag_batches.py and dag_queue read; unchanged."""
import json, pathlib
import dag_queue as dq, assumed
from own_decl import sorries, own

R = pathlib.Path(__file__).resolve().parent.parent
ROUTE = {}


def ids(f):
    p = R / f
    return [l.split()[0] for l in p.read_text().splitlines() if l.strip() and not l.lstrip().startswith("#")] if p.exists() else []


def targets():
    T = {3: set(ids("coord/nodes-batch3-targets.txt")), 4: set(ids("coord/nodes-batch4-targets.txt")),
         5: set(ids("coord/nodes-batch5-targets.txt"))}
    T[2] = set(t for t in ids("coord/new-targets.txt") if not any(t in v for v in T.values()))
    return T


def convention(d):
    l = d.get("lean"); return isinstance(l, dict) and bool(l.get("convention"))


QUARANTINED = None   # set by classify(): modules in quarantine with a rework row


def mathlib(d):
    # 2026-10-26: a stage-2 binding to an existing Mathlib declaration (`lean.existing`, module Mathlib.*) is a Mathlib node
    # too; before, own_decl.sorries() returned -1 for it and the walk counted it as a missing module and walked on below it
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    if l.get("existing") and str(l.get("module") or "").startswith("Mathlib."):
        return True
    return str(d.get("status")) == "mathlib" or bool(d.get("mathlib_match")) or dq.is_leaf(d)


def keeps(i):
    try: return dq.keeps_plan(i)
    except Exception: return False


def node_decls(d):
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    return ([l["declaration"]] if l.get("declaration") else []) + list(l.get("declarations") or [])


def route_decls(b):
    """the batch's own sorry route (local/sorry-route.json, else the newer partial walk local/sorry-route-failed.json)"""
    key = f"batch{b}"
    for f in ("local/sorry-route.json", "local/sorry-route-failed.json"):
        try:
            d = json.load(open(R / f))
        except Exception:
            continue
        o = (d.get("own") or {}).get(key)
        if o:
            ROUTE[b] = f
            return {x for v in o.values() for x in v} - set(assumed.decls_for(key))
    ROUTE[b] = None
    return set()


def split_since_route(imports=None) -> set:
    """modules new since the sorry route's commit, as tools/queue.py stage3() selects them: sorry_route.changed_in_batches
    minus the modules that existed (git ls-tree lean/) at the route's commit. Empty without a route or its commit."""
    import subprocess, sorry_route
    route = sorry_route.load()
    if route is None or not route.get("commit"):
        return set()
    if imports is None:
        import leanindex as li
        imports = li.scan()[1]
    changed = sorry_route.changed_in_batches(route, imports)
    old = subprocess.run(["git", "ls-tree", "-r", "--name-only", route["commit"], "--", "lean"], cwd=R,
                         capture_output=True, text=True)
    if old.returncode != 0:
        return set()
    existed = {p[len("lean/"):-len(".lean")].replace("/", ".") for p in old.stdout.split() if p.endswith(".lean")}
    return {m for m in changed if m not in existed}


BRIDGED = {}   # batch -> the nodes the split-since-route bridge started the walk at (report mode, or `split` given)
FIRST = {}     # batch -> the nodes of the walk before the bridge: the default walk (report=False, no `split`)


def split_nodes(g, mods) -> set:
    """the live nodes recorded in the modules `mods` (split_since_route())"""
    return {i for i, d in g.live.items() if dq.module_of(d) in mods}


def bridge_step(g, parents, split, seen) -> set:
    """the bridge rule, shared by classify() and tools/queue.py (the human, 2026-10-26): the nodes of `split` (nodes of
    modules new since the route) that a node of `parents` lists in its dependencies, not yet in `seen`"""
    return {g.resolve(c) for p in parents for c in g.deps(p, "all")} & split - set(seen)


def classify(g, T=None, report=False, split=None):
    """{batch: {node: class}}, and {batch: route sorries with no node}. report=True: the split-since-route bridge and the
    "blocked by rework" class (module docstring). `split` (the nodes of split_since_route(), tools/queue.py): the bridge
    without the report classes; FIRST keeps each batch's walk before the bridge"""
    live = g.live; T = T or targets(); out, nonode = {}, {}
    split, rw_mods = set(split or ()), set()
    if report:
        import leanindex as li, rework
        imports = li.scan()[1]
        if not split:
            split = split_nodes(g, split_since_route(imports))
        rw_rows = rework.load()
        if rw_rows:   # the modules tools/queue.py leaves out: blocked by rework, or still in quarantine
            rw_mods = rework.blocked(g, imports, rw_rows)[1] | {m for m in rw_rows if not rework.landed(m)}
    BRIDGED.clear(); FIRST.clear()
    for b in sorted(T):
        others = set().union(*(T[o] for o in T if o != b)) - T[b]
        A = set(assumed.nodes_for(f"batch{b}")) if hasattr(assumed, "nodes_for") else set()
        global QUARANTINED
        if QUARANTINED is None:
            try:
                import rework as _rw
                QUARANTINED = {m for m in _rw.load() if not _rw.landed(m)}
            except Exception:  # noqa: BLE001
                QUARANTINED = set()
        cls = {}
        rdecls = route_decls(b)
        st = [i for i, d in live.items() if any(x in rdecls for x in node_decls(d))]
        st += [t for t in T[b] if t in live]; seen = set()
        covered = {x for i in st for x in node_decls(live[i]) if x in rdecls}
        nonode[b] = sorted(rdecls - covered)
        bridged = set()
        while True:
            while st:
                i = g.resolve(st.pop())
                if i in seen or i not in live: continue
                seen.add(i)
                if i in others: continue
                d = live[i]
                if convention(d) or mathlib(d): continue
                if i in A: cls[i] = "assumed"; continue
                m = dq.module_of(d)
                # 2026-10-24 (the human): a node whose own proof is written is done even when it rests on a `sorry` below:
                # that sorry is the work of the node recording it (the route gives every route sorry a node), counted there.
                # Only a sorry in the node's own declaration keeps it open, read from the live text: the audit
                # (dag/lean_audit.json) is computed from the last published build and lags behind landed proofs.
                o = own(d, m)
                if dq.finished(d) or o is False: cls[i] = "done"; continue
                if str(d.get("status")) == "unsplit" and not keeps(i):
                    cls[i] = "stage 1 (unsplit)"; continue
                if not dq.stated_node(d): cls[i] = "stage 2 (no Lean statement)"
                elif m and sorries(m) == -1:
                    cls[i] = "rework (module quarantined/missing)"
                    # 2026-10-26: a module quarantined by a red build (a rework row) failed to compile; its proof is
                    # written and its rework item restores it. The walk does not go below it: going below opened ~800
                    # off-route modules when a 240-module quarantine reached a route node (14:31). A module that is
                    # missing without a rework row is walked through as before.
                    if m in QUARANTINED:
                        continue
                elif i in bridged: cls[i] = "stage 3 (split since route)"
                elif m in rw_mods: cls[i] = "stage 3 (blocked by rework)"
                else: cls[i] = "stage 3 (Lean has sorry)"
                st += [x for x in g.deps(i, "all")]
            if b not in FIRST:
                FIRST[b] = set(cls)
            # report mode, the bridge: nodes of modules split since the route with a DAG parent in this walk (done or
            # not) start the walk; repeated until no new one (a split-off lemma may itself have split-off children)
            new = bridge_step(g, cls, split, seen)
            if not new: break
            bridged |= new; st = list(new)
        BRIDGED[b] = bridged
        out[b] = cls
    return out, nonode


def open_nodes(g) -> set:
    """every node some batch's walk reaches and does not count done"""
    cls, _ = classify(g)
    return {i for c in cls.values() for i, k in c.items() if k not in ("done", "assumed")}


# 2026-10-27 (the human): the TOTAL of a route in the reports. The walk above stops below a node whose own proof is
# written and at modules quarantined by a red build, so done + open of the walk shrank as work got done (batch 3: 670 at
# 02:05, 112 at 15:05): the done nodes below a finished parent, its split children among them, dropped out. Report only;
# classify() and the queue are unchanged.
#   total = the open nodes of the walk (remaining, unchanged) + every DONE node of the route: reached from the targets
#   and the open nodes through stmt_deps, proof_deps and step `uses`, going on THROUGH done nodes. Not counted and not
#   entered: another batch's target, conventions, Mathlib leaves, a node neither open in the walk nor done (a plan node
#   the Lean route bypassed, or a sorried declaration the route does not use). Assumed nodes count as done and are not
#   entered (as in the walk). A node of a quarantined module counts with its last state, read from its quarantined copy.
def _quarantine_own(d, m):
    """own() read from the quarantined copy quarantine/<path>: False (own proof written), True (sorry), None (unknown)"""
    import re, leanindex as li, own_decl as od
    p = R / "quarantine" / pathlib.Path(*m.split(".")).with_suffix(".lean")
    if not p.is_file():
        return None
    t = p.read_text(errors="ignore")
    if li.sorry_count(t) == 0:
        return False
    names = node_decls(d)
    if not names:
        return None
    t = od._COMMENTS.sub("", t)
    starts = [x.start() for x in od._DECL.finditer(t)] + [len(t)]
    blocks = [t[a:b] for a, b in zip(starts, starts[1:])]
    r = []
    for n in names:
        hit = [b for b in blocks if (x := od._declared(b)) and (n == x or n.endswith("." + x))]
        r.append(any(od._block_sorry(b) for b in hit) if hit else None)
    return True if any(x is True for x in r) else False if all(x is False for x in r) else None


def node_done(g, i, A=()) -> bool:
    """done for the route total: assumed, finished (dag_queue), own proof written in live, or (quarantined module) in
    its quarantined copy"""
    d = g.live[i]
    if i in A or dq.finished(d):
        return True
    m = dq.module_of(d)
    if not m:
        return False
    o = own(d, m)
    if o is None and sorries(m) == -1:
        o = _quarantine_own(d, m)
    return o is False


def route_done(g, starts, opn, others=(), A=(), done=None) -> set:
    """the done nodes of a route (see above): walk from `starts` (the targets and the nodes of the progress walk) and
    `opn` (its open nodes) through open and done nodes; `done(i)` decides done (default node_done)"""
    done = done or (lambda i: node_done(g, i, A))
    out, seen, st = set(), set(), [g.resolve(x) for x in list(starts) + list(opn)]
    while st:
        i = g.resolve(st.pop())
        if i in seen or i not in g.live: continue
        seen.add(i)
        if i in others and i not in opn: continue
        d = g.live[i]
        if convention(d) or mathlib(d): continue
        if i in opn:
            pass
        elif done(i):
            out.add(i)
            if i in A: continue
        else:
            continue   # bypassed plan node, or a sorried declaration off the route: neither counted nor entered
        st += [c for c in g.deps(i, "all") if c not in seen]
    return out - set(opn)


def route_totals(g, cls, T=None) -> dict:
    """{batch: (open nodes, done nodes)} for the reports; `cls` from classify(g, T, report=True)"""
    T = T or targets(); out = {}
    for b, c in cls.items():
        others = set().union(*(T[o] for o in T if o != b)) - T[b]
        A = set(assumed.nodes_for(f"batch{b}")) if hasattr(assumed, "nodes_for") else set()
        opn = {i for i, k in c.items() if k not in ("done", "assumed")}
        out[b] = (opn, route_done(g, set(T[b]) | set(c), opn, others, A))   # every node of the walk starts it
    return out
