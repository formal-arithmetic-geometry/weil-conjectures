#!/usr/bin/env python3
"""The items of stages 1 and 2, read from the DAG, and the modules that stage 3 must still wait for.

Usage:
  tools/dag_queue.py summary      how many nodes each stage has open, and why the others are not open
  tools/dag_queue.py items        the open items, one per line: stage, item, distance (to a target in stage 1, to Mathlib in stage 2),
                                  kind (in stage 1 the node's lean_audit state on the done branch), in stage 2 also blockers
  tools/dag_queue.py waiting      modules whose node depends (stmt_deps, proof_deps, the `uses` of the proof steps) on a node
                                  that has no Lean declaration yet, one per line

`queue.py write` calls this and puts the items into coord/queue.tsv; run this by hand only to look.

What is open follows the stage documents. A node that no target reaches is not open for any stage. A node is open for

  stage 1  (SETUP.md, requirements of 2026-10-09) when a target reaches it without passing through a finished
           node, and it is neither finished, nor a Mathlib leaf, nor split. A node is finished when its
           `lean_audit` state on the branch SHEAF_DONE_BRANCH (default slopmaster2) is `closed`: its Lean exists
           and no `sorry` is reachable from it, or an isolated-project lead record binds a completed first-task
           assignment to its current interface. Nothing below a finished assignment is an item. A node is split only when a
           worker has checked it against stages/1-dag.md (`status` is `split`) and the lead has reviewed that
           (`reviewed` is set); the `imported` status of the blueprint import does not count. Every other
           reached node (states none, sorry_here, rests_on_sorry, closed_part) is an item, nearest to a
           target first, the distance counted through unfinished nodes only; since 2026-10-09 the order is first the rank of the
           node's unit on the targets' unit route (tools/units.py route; units outside the route last), then the distance
           (the key printed by `items` is rank*1000 + distance);
  stage 2  when stage 1 has split it (a definition naming the notions it is built from, or a statement with its proof in steps),
           it has no Lean declaration yet, and every node its statement needs is stated: it has a `lean` record, is a
           Mathlib leaf, is assumed, or is finished with its declaration existing upstream (closed on SHEAF_DONE_BRANCH:
           the audit record's `decls` name the declarations in slopmaster2, which live imports verbatim; a recorded
           completion; a live module closed in stage 3) -- the human, 2026-10-18: before, a finished node without a
           `lean` record held back every node whose statement needs it, with "a stmt_dep has no Lean statement";
           a node below a finished node (not reached by stage 1) is still an item when the statement of a reached node
           needs it (the stmt_deps closure of the reached nodes needing a statement, tools/dag_queue.py stmt_needed);
           definitions before statements (launcher, 2026-10-11); then, blockers first (human, 2026-10-11 23:30 +08), the
           item that the most stage-2 nodes still needing a statement wait for, counted transitively through stmt_deps
           (`items` prints the count last, queue.tsv as the column `blockers`); ties nearest to Mathlib first (the
           fewest dependency steps down to a Mathlib leaf), so that the statements climb from Mathlib upward. With SHEAF_EARLY_REVIEW=1 in coord/sheaf.env the nodes
           needed to state the targets come first instead.

A module of stage 3 is held back ("waiting") while a node that its node depends on, through stmt_deps or proof_deps
(the human, 2026-10-18; proof_deps only from 2026-10-17), has no Lean declaration: its proof cannot be written yet.
The order of the dependencies is never overridden: no node is stated before the nodes its statement needs, so stage 2
climbs from Mathlib upward whatever order stage 1 or stage 3 keep.

The DAG layout is the project's own (`stages/1-dag.md` §1 fixes the content, not the field names). The FIELDS
table below lists the names this script accepts for each piece of content; the maintainer adapts it to the
project's layout, as `tools/README.md` says. `SHEAF_DAG` in coord/sheaf.env names the node directory when it is
not `dag/nodes`.
"""
from __future__ import annotations
import collections, hashlib, json, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

# content -> field names tried in order; the first present wins
FIELDS = {
    "id": ("id",),
    "kind": ("kind", "role"),                       # definition / statement / target
    "target": ("target",),                          # true for a target
    "status": ("status",),                          # 'mathlib' (a leaf), 'split', 'merged', ...
    "mathlib": ("mathlib_match", "mathlib"),        # the Mathlib match of a leaf, if any
    "merged": ("merged_into",),                     # the node this one was merged into
    "stmt_deps": ("stmt_deps", "statement_deps", "deps"),
    "proof_deps": ("proof_deps",),
    "proof": ("proof", "steps"),                    # the proof in steps; each step may list what it uses
    "module": ("module", "lean_module"),            # set when the node has a Lean declaration
    "lean": ("lean",),                              # or a record {module, declaration, ...}
    "audit": ("lean_audit",),                       # {branch: {state: none|closed|closed_part|sorry_here|rests_on_sorry, ...}}
    "reviewed": ("reviewed",),                      # set by the lead when the review of a split passed
}
DONE_STATES = {"closed"}                            # audit states on SHEAF_DONE_BRANCH that finish a node for stage 1
DEF_KINDS = {"def", "definition", "stmt", "notion", "structure"}
LEAF_STATUS = {"mathlib", "exact", "adapt"}


def field(d: dict, name: str):
    for f in FIELDS[name]:
        if f in d and d[f] not in (None, "", [], {}):
            return d[f]
    return None


def nodes_dir() -> pathlib.Path:
    p = li.config().get("SHEAF_DAG", "dag/nodes")
    return pathlib.Path(p) if pathlib.Path(p).is_absolute() else li.ROOT / p


def load() -> dict[str, dict]:
    out = {}
    for p in sorted(nodes_dir().rglob("*.json")):
        try:
            d = json.loads(p.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(d, dict) and field(d, "id"):
            out[str(field(d, "id"))] = d
    return out


def is_leaf(d) -> bool:
    st = field(d, "status")
    return str(st).lower() in LEAF_STATUS if st else bool(field(d, "mathlib"))


def done_branch() -> str:
    return li.config().get("SHEAF_DONE_BRANCH", "slopmaster2")


def audit_state(d) -> str:
    a = field(d, "audit")
    if isinstance(a, dict):
        b = a.get(done_branch())
        if isinstance(b, dict) and b.get("state"):
            # 2026-10-15: upstream's blueprint reader iterated a Lean record as
            # dictionary keys, inventing missing declarations branch/declarations/note.
            # Ignore only that exact metadata failure after checking all explicitly
            # recorded declarations; partial docstring tags must never close a node.
            rec = d.get("lean") or {}
            missing = set(b.get("missing") or [])
            complete = {r["name"] for r in b.get("decls", []) if isinstance(r, dict)
                        and r.get("name") and not r.get("partial") and not r.get("sorry")}
            wanted = set(rec.get("declarations") or []) | ({rec["declaration"]} if rec.get("declaration") else set())
            own_closed = (rec.get("branch") == done_branch() and wanted and wanted <= complete
                          and not b.get("open") and not any(r.get("sorry") for r in b.get("decls", [])))
            if (b["state"] == "closed_part" and missing and "branch" in missing
                    and missing <= {"branch", "declarations", "note"} and own_closed):
                return "closed"
            # 2026-10-18 (s1loop; closed_part decided explicitly): a partial closure finishes the node when the node's own
            # declarations are closed, and "own" means an attachment (tools/attach.py: two workers confirmed that these
            # declarations state the node exactly) on the done branch, every one of them sorry-free in this audit record.
            # The other names the audit misses are then names of the blueprint tag (lem-sfb-modobj-abelian: master's
            # CategoryTheory.Mod.instAbelian_weilConjectures for slopmaster2's CategoryTheory.Mod.instAbelian), not
            # clauses of the node. A `lean` record taken from lean_audit for stage 2 asserts no such coverage
            # (lem-fd-as-lisse records the lisse clause only), so it stays an item.
            if (b["state"] == "closed_part" and own_closed
                    and str(rec.get("note") or "").startswith("attached by the lead's tool")):
                return "closed"
            return str(b["state"])
    return "none"


_COMPLETIONS: dict = {}


def recorded_stage1_completion(d) -> bool:
    # 2026-10-15: live Sheaf proofs/first-task ownership are not slopmaster2
    # attachments. Honor explicit lead records, bound to the statement and Lean
    # interface, so new-targets never tries to split those completed assignments.
    # A changed statement/interface invalidates the record; rank alone never does.
    path = li.ROOT / "coord/newtargets-stage1-completions.json"
    try:
        st = path.stat()
    except OSError:
        return False
    key = (st.st_mtime_ns, st.st_size)   # 2026-10-17 (cpu): parsed once per process, not once per node
    if _COMPLETIONS.get("key") != key:
        _COMPLETIONS.update(key=key, data=json.loads(path.read_text()))
    rec = _COMPLETIONS["data"].get(str(field(d, "id")))
    if not isinstance(rec, dict) or rec.get("by") != "L-only":
        return False
    payload = {k: d.get(k) for k in ("statement", "lean")}
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    declarations = {(d.get("lean") or {}).get("declaration")} | set((d.get("lean") or {}).get("declarations") or [])
    audit = (d.get("lean_audit") or {}).get(done_branch()) or {}
    declarations.update(x.get("name") for x in audit.get("decls", []) if not x.get("sorry"))
    audit_digest = hashlib.sha256(json.dumps(audit, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    return (rec.get("result") == "complete" and rec.get("interface_sha256") == digest
            and rec.get("basis") in ("live-proved", "first-task-existing-declaration")
            and bool(rec.get("declaration")) and rec["declaration"] in declarations
            and (not rec.get("audit_sha256") or rec["audit_sha256"] == audit_digest))


_NOTES: dict = {}


def repair_note(i: str) -> dict:
    """coord/repair-notes/<i>.json, {} when absent or unreadable (parsed once per file version)."""
    p = li.ROOT / "coord" / "repair-notes" / (i + ".json")
    try:
        st = p.stat()
    except OSError:
        return {}
    key = (st.st_mtime_ns, st.st_size)
    hit = _NOTES.get(i)
    if hit and hit[0] == key:
        return hit[1]
    try:
        r = json.loads(p.read_text())
        r = r if isinstance(r, dict) else {}
    except (OSError, ValueError):
        r = {}
    _NOTES[i] = (key, r)
    return r


def keeps_plan(i: str) -> bool:
    """the human, 2026-10-17: a coarse split returned for re-splitting keeps its route (its long steps only gain cited
    nodes), so its dependencies stay reached and their work stays open; marked by `keep_plan` in its released repair note."""
    r = repair_note(i)
    return r.get("state") == "released" and bool(r.get("keep_plan"))


def stage1_repair_owed(i: str) -> bool:
    """2026-10-18 (s1loop): a released stage-1 repair note (a split returned for re-splitting or repair, keep_plan or not)
    is owed until a stage-1 delivery that resolves it lands; the landing marks it resolved (resolve_stage1_note). A note
    without `stage` is a stage-1 return of the 2026-10-16 literature re-review (stage-3 notes are keyed by module names,
    which are not node ids)."""
    r = repair_note(i)
    return r.get("state") == "released" and str(r.get("stage") or "1") == "1"


def resolve_stage1_note(i: str, by: str) -> bool:
    """Mark a released stage-1 repair note resolved by the landing `by`; the caller commits the file. True if changed."""
    if not stage1_repair_owed(i):
        return False
    p = li.ROOT / "coord" / "repair-notes" / (i + ".json")
    r = dict(repair_note(i))
    r["state"] = "resolved"
    r["resolved_by"] = by
    p.write_text(json.dumps(r, indent=1, ensure_ascii=False) + "\n")
    return True


def closed_upstream(d) -> bool:
    """The node's Lean declaration exists in a module the project imports, with or without a `lean` record of its own:
    its audit state on the done branch is closed (the declaration is in slopmaster2, which live imports verbatim; the
    audit record's `decls` name it, module and lines), a lead record binds a completed first-task assignment to a named
    declaration (recorded_stage1_completion: basis live-proved or first-task-existing-declaration, the declaration one
    of the node's `lean` record or of the audit's sorry-free decls), or its recorded live module is closed in stage 3."""
    import live_closed   # the human, 2026-10-16: what stage 3 finished in the live project prunes stage 2 below it
    return audit_state(d) in DONE_STATES or recorded_stage1_completion(d) or live_closed.node_closed(d)


def finished(d) -> bool:
    """Closed Lean or an interface-bound isolated lead completion finishes stage 1 for this assignment."""
    if assumed_done(d):   # the human, 2026-10-17: a node its batches assume (coord/assumed.tsv)
        return True
    return closed_upstream(d)


def stated_node(d) -> bool:
    """The node has its Lean statement, read from the node alone (Dag.stated adds the assumed nodes): a Mathlib leaf, a
    `lean` record, or closed upstream. The human, 2026-10-18: a finished node is stated; before, a node finished through
    the audit but without a `lean` record held back every node whose statement needs it."""
    return is_leaf(d) or has_decl(d) or closed_upstream(d)


# the human, 2026-10-17 (batch 5 ASSUMES the Lefschetz trace formula and Poincare duality; their Lean keeps its `sorry`):
# the nodes listed in coord/assumed.tsv (tools/assumed.py) are finished for the batches that assume them. Such a node is
# finished when every target that reaches it belongs to a batch assuming it (coord/nodes-batchN-targets.txt; a target in no
# batch file assumes nothing). Finished, it is never a stage-1 or stage-2 item, counts as stated (nothing waits for it),
# and its stmt_deps are not reached through it.
_ASSUMED: dict = {}


def target_batches() -> dict[str, str]:
    out = {}
    # retirement of ~/weil-newtargets (2026-10-19): the node-id target lists of the batches are coord/nodes-batchN-targets.txt
    # (coord/batchN-targets.txt list the stage-3 target MODULES of the same batches)
    for p in sorted((li.ROOT / "coord").glob("nodes-batch*-targets.txt")):
        m = re.fullmatch(r"nodes-batch(\d+)-targets\.txt", p.name)
        if not m:
            continue
        for x in p.read_text().splitlines():
            if x.strip() and not x.lstrip().startswith("#"):
                out.setdefault(x.split()[0], f"batch{m.group(1)}")
    return out


def assumed_done(d) -> bool:
    if "done" not in _ASSUMED:
        import assumed
        if assumed.nodes():
            g = Dag.__new__(Dag); g._graph(load()); g._set_assumed()
        else:
            _ASSUMED["done"] = set()
    return str(field(d, "id")) in _ASSUMED["done"]


def is_def(d) -> bool:
    return str(field(d, "kind") or "").lower() in DEF_KINDS


def has_decl(d) -> bool:
    if field(d, "module"):
        return True
    l = field(d, "lean")
    if isinstance(l, dict) and l.get("convention"):   # a convention node (L, 2026-10-11): fixes no notion, stands for no declaration
        return True
    return bool(l.get("module") if isinstance(l, dict) else l)


def module_of(d):
    m = field(d, "module")
    if m:
        return str(m)
    l = field(d, "lean")
    return str(l.get("module")) if isinstance(l, dict) and l.get("module") else None


def unfolded(d) -> bool:
    """Stage 1 is done with the node: a Mathlib leaf, a finished node (its Lean closed), or a node a worker has
    split (`status` split) and the lead has reviewed (`reviewed` set). An imported, unchecked node is not split."""
    if is_leaf(d) or finished(d):
        return True
    # 2026-10-18 (s1loop): a split with a released stage-1 repair note is not done until the repairing delivery lands
    if stage1_repair_owed(str(field(d, "id"))):
        return False
    return str(field(d, "status") or "").lower() == "split" and bool(field(d, "reviewed"))


def stage1_completed(d) -> bool:
    """THE stage-1 completion predicate (2026-10-18, s1loop): stage1() lists exactly the reached nodes for which it is
    false, tools/claim.py node_finished (stage 1) refuses claims and tools/retire_stage1.py archives deliveries exactly
    when it is true. unfolded() (a Mathlib leaf; closed upstream, including an attached closed_part; or a reviewed split
    with no owed repair note) or a node merged into another."""
    # 2026-10-21 (the human): a released stage-1 repair note (a re-split) reopens the node whatever else closed it
    if d is not None and stage1_repair_owed(str(d.get("id") or "")):
        return False
    return unfolded(d) or str(field(d, "status") or "").lower() == "merged"


def queue_nodes_dir() -> pathlib.Path:
    """The DAG the queue reads (SHEAF_DAG of coord/sheaf.env and the machine file), whatever SHEAF_DAG the calling
    process sets: the landing tools set SHEAF_DAG=dag/nodes (this project's copy) for their own checks."""
    import socket, shlex
    val = None
    for p in (li.ROOT / "coord" / "sheaf.env", li.ROOT / "coord" / "machines" / f"{socket.gethostname()}.env"):
        try:
            lines = p.read_text().splitlines()
        except OSError:
            continue
        for line in lines:
            line = line.split("#", 1)[0].strip()
            if "=" in line and line.split("=", 1)[0].strip() == "SHEAF_DAG":
                val = " ".join(shlex.split(line.split("=", 1)[1]))
    p = pathlib.Path(val or "dag/nodes")
    return p if p.is_absolute() else li.ROOT / p


def queue_node(i: str):
    """The node record the queue reads for `i`, or None."""
    for p in queue_nodes_dir().glob(f"*/{i}.json"):
        try:
            return json.loads(p.read_text())
        except (OSError, ValueError):
            return None
    return None


def deps_of(d, which: str) -> list[str]:
    out = []
    if which in ("stmt", "all"):
        out += [str(x) for x in (field(d, "stmt_deps") or [])]
    if which in ("proof", "all"):
        out += [str(x) for x in (field(d, "proof_deps") or [])]
        pf = field(d, "proof")
        if isinstance(pf, list):
            for step in pf:
                if isinstance(step, dict):
                    out += [str(x) for x in (step.get("uses") or [])]
    return out


class Dag:
    def __init__(self, nodes: dict[str, dict]):
        self._graph(nodes)
        self._set_assumed()
        self.dist = self.distances(cut=False)    # every node a target reaches: the DAG check and stages 2 and 3
        self.dist1 = self.distances(cut=True)    # reached without passing through a finished node: stage 1
        self.height = {}   # fewest dependency steps down to a Mathlib leaf

    def _set_assumed(self):
        """self.assumed: the nodes of coord/assumed.tsv that are finished here (every target reaching them is of a batch
        that assumes them); also the module-wide set read by finished()."""
        import assumed
        recs = {i: bs for i, bs in assumed.nodes().items() if i in self.live}
        done = set()
        if recs:
            tb, tset = target_batches(), set(self.targets)
            rev = collections.defaultdict(set)
            for j, d in self.live.items():
                for c in deps_of(d, "all"):
                    rev[self.resolve(c)].add(j)
            for i, bs in recs.items():
                seen, st = {i}, [i]
                while st:
                    for q in rev.get(st.pop(), ()):
                        if q not in seen:
                            seen.add(q); st.append(q)
                if all(tb.get(t) in bs for t in seen & tset):
                    done.add(i)
        _ASSUMED["done"] = self.assumed = done

    def batch_reach(self, batch, roots) -> dict[str, int]:
        """what the targets `roots` of `batch` reach, not entering the nodes that batch assumes (coord/assumed.tsv)"""
        import assumed
        return self.distances_from(roots, stop=assumed.nodes_for(batch))

    def _graph(self, nodes: dict[str, dict]):
        self.n = nodes
        self.merged = {i: str(field(d, "merged")) for i, d in nodes.items()
                       if field(d, "merged") or str(field(d, "status") or "").lower() == "merged"}
        self.live = {i: d for i, d in nodes.items() if i not in self.merged}
        target_file = li.config().get("SHEAF_TARGET_LIST")
        if target_file:
            tp = pathlib.Path(target_file)
            if not tp.is_absolute(): tp = li.ROOT / tp
            wanted = {x.strip() for x in tp.read_text().splitlines() if x.strip() and not x.lstrip().startswith("#")} if tp.exists() else set()
            self.targets = [i for i in wanted if i in self.live]
        else:
            self.targets = [i for i, d in self.live.items() if field(d, "target") or str(field(d, "kind") or "").lower() == "target"]

    def distances(self, cut: bool) -> dict[str, int]:
        # the human, 2026-10-16: "先放开一批 batch3 下面的子节点，后面不用再剪枝，别干等着" -- nodes listed in
        # coord/preopen.txt are reached like targets (their work opens before the parent's split lands, and stays open
        # even if that split later changes)
        pre = li.ROOT / "coord" / "preopen.txt"
        extra = [x.split()[0] for x in pre.read_text().splitlines() if x.strip() and not x.lstrip().startswith("#")] if pre.exists() else []
        return self.distances_from(list(self.targets) + [x for x in extra if x in self.live and x not in self.targets], cut)

    def distances_from(self, roots, cut: bool = False, stop=()) -> dict[str, int]:
        dist = {}
        dq = collections.deque((t, 0) for t in roots)
        while dq:
            i, k = dq.popleft()
            if i in dist:
                continue
            dist[i] = k
            if i in stop:
                continue
            if cut and finished(self.live[i]):
                continue
            # launcher, 2026-10-16 (the human: pruned content is not reported as unfinished): an unsplit node is to be
            # (re)split; the dependencies it still lists are a returned split's old plan, which the redo may prune, so
            # they are not reached through it
            if str(field(self.live[i], "status") or "").lower() == "unsplit" and not keeps_plan(i):
                continue
            for c in deps_of(self.live[i], "all"):
                c = self.resolve(c)
                if c in self.live and c not in dist:
                    dq.append((c, k + 1))
        return dist

    def h(self, i: str, stack=()) -> int:
        if i in self.height:
            return self.height[i]
        d = self.live.get(i)
        if d is None or is_leaf(d):
            return 0
        if i in stack:
            return 10**6
        below = [self.h(c, stack + (i,)) for c in self.deps(i, "all")]
        self.height[i] = 1 + (min(below) if below else 0)
        return self.height[i]

    def resolve(self, i: str) -> str:
        seen = set()
        while i in self.merged and i not in seen:
            seen.add(i); i = self.merged[i]
        return i

    def deps(self, i: str, which: str) -> list[str]:
        d = self.live.get(i)
        if d is None:   # a cited node whose file is missing: check_dag.py reports it as "deps: ... no such node" (never a crash)
            return []
        return [self.resolve(c) for c in deps_of(d, which)]

    def stated(self, i: str) -> bool:
        d = self.live.get(i)
        # an assumed node is stated (2026-10-17); a finished node is stated (2026-10-18, stated_node); a dependency on a
        # missing node is reported by the DAG check, not here
        return d is None or i in self.assumed or stated_node(d)

    def stmt_needed(self, roots) -> set[str]:
        """The unstated nodes the statements of `roots` need, transitively through stmt_deps (the human, 2026-10-18): a
        node outside dist1 (reached only through a finished node) that is in this closure of a reached node needing a
        statement is a stage-2 item like any other, not "below a finished node, not needed". The walk stops at stated
        nodes and, as stage1() does, does not descend from a node that is not split unless it keeps its plan (its listed
        dependencies are an old plan the redo may prune)."""
        out, seen, stack = set(), set(), list(roots)
        while stack:
            i = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            d = self.live.get(i)
            if d is None or (not unfolded(d) and not keeps_plan(i)):
                continue
            for c in self.deps(i, "stmt"):
                if c in self.live and c not in seen and not self.stated(c):
                    out.add(c); stack.append(c)
        return out

    def stage1(self) -> list[tuple[int, str]]:
        """nearest to a target first; since 2026-10-09 (SETUP.md) ordered first by the unit route: the rank of the node's unit in
        the breadth-first walk of the units from the targets' units through `uses` (tools/units.py route), nodes of units
        outside the route last, then by distance."""
        try:
            import units as un
            rank = {u: k for k, u, _ in un.route(self.n)}
        except Exception:
            rank = {}
        big = 10**6
        # A released human re-split reopens even closed Lean. Use the same
        # completion predicate as claims and retirement, rather than unfolded().
        items = [((rank.get(self.live[i].get("unit"), big) if rank else 0) * 1000 + self.dist1[i], i)
                 for i, d in self.live.items() if i in self.dist1 and not stage1_completed(d)]
        # the human, 2026-10-16 (STAGE 1 -> 2 HANDOFF): an unsplit node in the statement downstream (stmt_deps closure) of a
        # node on the reach blocks that statement's grounding; it is a stage-1 item even when the target route does not pass
        # through it (it was never offered: the route reaches it only through stmt_deps of nodes behind finished ones)
        have = {i for _, i in items}
        # 2026-10-17: an assumed node's stmt_deps are not pulled in through it
        seen, stack = set(), [c for i in self.dist if i not in self.assumed for c in self.deps(i, "stmt")]
        while stack:
            c = stack.pop()
            if c in seen: continue
            seen.add(c)
            d = self.live.get(c)
            if d is None or ((is_leaf(d) or finished(d)) and not stage1_repair_owed(c)): continue
            if not stage1_completed(d):
                if c not in have: items.append((big * 1000 + self.dist.get(c, 999), c)); have.add(c)
                if not keeps_plan(c):   # 2026-10-17: a returned coarse split keeps its plan; its statement downstream stays open
                    continue
            stack.extend(self.deps(c, "stmt"))
        return sorted(items)

    def stage1_states(self) -> collections.Counter:
        return collections.Counter(audit_state(self.live[i]) for _, i in self.stage1())

    def target_statement_closure(self) -> set[str]:
        out, st = set(), list(self.targets)
        while st:
            i = st.pop()
            if i in out or i not in self.live:
                continue
            out.add(i); st += self.deps(i, "stmt")
        return out

    def needs_statement(self, i: str) -> bool:
        """A stage-2 node that still needs a statement: reached from a target and not stated (no Lean declaration of its
        own, not a Mathlib leaf, not assumed, not finished with its declaration upstream)."""
        return i in self.live and i in self.dist and not self.stated(i)

    def blockers(self, items) -> dict[str, int]:
        """item -> how many stage-2 nodes still needing a statement cannot be stated before it: every node whose stmt_deps
        chain reaches the item (transitively, each counted once, the item itself excluded). Reverse stmt_deps graph, one
        walk per item."""
        rev = collections.defaultdict(set)
        for j in self.live:
            for c in self.deps(j, "stmt"):
                if c != j:
                    rev[c].add(j)
        out = {}
        for i in items:
            seen, st = {i}, [i]
            while st:
                for p in rev.get(st.pop(), ()):
                    if p not in seen:
                        seen.add(p); st.append(p)
            out[i] = sum(1 for j in seen if j != i and self.needs_statement(j))
        return out

    def stage2(self) -> tuple[list[tuple[int, int, str, int]], collections.Counter]:
        """(priority, height, node, blockers): definitions first, then the most blocking first (human, 2026-10-11 23:30 +08),
        then nearest to Mathlib; the targets' statement closure first when the early review is on."""
        why = collections.Counter(); items = []; tsc = self.target_statement_closure()
        s1open = {nid for _, nid in self.stage1()}
        early = li.config().get("SHEAF_EARLY_REVIEW", "") not in ("", "0", "no")
        # the human, 2026-10-18: a node below a finished node is still needed when the statement of a reached node needs it
        need = self.stmt_needed([i for i in self.dist1 if self.needs_statement(i)])
        for i, d in self.live.items():
            if not self.needs_statement(i):   # a leaf, stated, assumed (never an item, 2026-10-17) or finished (2026-10-18)
                continue
            if i not in self.dist1 and i not in need:
                # launcher, 2026-10-15: reached only through a node whose Lean is already closed. Stage 1 does not split such
                # nodes (stage1 uses dist1), and no target needs their statements; they were counted as "waits for stage 1".
                why["below a finished node, not needed"] += 1; continue
            # human, 2026-10-16 (STAGE 1 -> 2 HANDOFF): a statement is formalized bottom-up, and only once its STATEMENT
            # downstream is grounded in Mathlib: the node itself is split (stage 1 done) and every statement dependency
            # (stmt_deps; proof dependencies do not matter here) already has its Lean statement, which by the same rule
            # rests on a grounded downstream. This supersedes the morning's relaxation.
            # launcher, 2026-10-17: a coarse split returned for re-splitting (keep_plan) is re-split for its PROOF only; its
            # statement and stmt_deps stay, so its own statement is not held back by the re-split
            if not unfolded(d) and not keeps_plan(i):
                why["waits for stage 1 (statement downstream not grounded)"] += 1; continue
            if not all(self.stated(c) for c in self.deps(i, "stmt")):
                why["waits for a statement dependency (bottom-up)"] += 1; continue
            if not self.stmt_grounded(i):
                why["waits for stage 1 deeper in its statement downstream"] += 1; continue
            items.append((0 if early and i in tsc else 1, self.h(i), i))
        # launcher, 2026-10-11 10:50 UTC (STAGE 2 ORDER: DEFINITIONS FIRST): a statement cannot be written before its
        # definitions, so within the open items the definitions come first, then the statements, each by the order above.
        # human, 2026-10-11 23:30 +08 (STAGE 2 ORDER: BLOCKERS FIRST): after the definitions rule, the item that the most
        # stage-2 nodes wait for (transitively through stmt_deps) comes first; ties by the distance order above
        b = self.blockers([t[2] for t in items])
        items = [(pri, hgt, i, b[i]) for pri, hgt, i in items]
        return sorted(items, key=lambda t: (t[0], not is_def(self.live[t[2]]), -t[3], t[1], t[2])), why

    def stmt_grounded(self, i: str) -> bool:
        """Every node of the statement-dependency closure below i (stmt_deps only, not proof deps) is split, a Mathlib leaf
        or finished: the statement downstream is grounded in Mathlib (the human, 2026-10-16)."""
        memo = self.__dict__.setdefault("_grounded", {})
        seen, stack, ok = set(), list(self.deps(i, "stmt")), True
        while stack:
            c = stack.pop()
            if c in seen: continue
            seen.add(c)
            if c in memo:
                if not memo[c]: ok = False; break
                continue
            d = self.live.get(c)
            if d is None or is_leaf(d) or finished(d): continue
            if not unfolded(d) and not keeps_plan(c): ok = False; break   # 2026-10-17: a returned coarse split keeps its statement
            stack.extend(self.deps(c, "stmt"))
        memo[i] = ok
        return ok

    def waiting(self) -> list[tuple[str, str]]:
        """(module, node it waits for) for every stated node that depends on an unstated node: stmt_deps and proof_deps
        (the human, 2026-10-18: a node may be proved as soon as every statement it depends on, both stmt_deps and
        proof_deps, has a Lean statement; until then its module is not a stage-3 item)."""
        out = []
        for i, d in self.live.items():
            if is_leaf(d) or not has_decl(d) or not module_of(d):
                continue
            for c in self.deps(i, "all"):
                if not self.stated(c):
                    out.append((module_of(d), c)); break
        return sorted(out)


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "summary"
    if not nodes_dir().is_dir():
        raise SystemExit(f"no DAG at {nodes_dir()}")
    g = Dag(load())
    only_stage1 = li.config().get("SHEAF_OPEN_STAGES") == "1"
    s1 = g.stage1()
    s2, why, w = [], {}, []
    if not only_stage1:
        s2, why = g.stage2(); w = g.waiting()
    if cmd == "summary":
        print(f"nodes: {len(g.n)} ({len(g.merged)} merged, {sum(1 for d in g.live.values() if is_leaf(d))} Mathlib leaves, "
              f"{len(g.targets)} targets, {sum(1 for i in g.live if i not in g.dist)} not reached from a target)")
        print(f"stage 1 open: {len(s1)} nodes to split (" + ", ".join(f"{v} {k}" for k, v in sorted(g.stage1_states().items()))
              + f"); finished: {sum(1 for d in g.live.values() if finished(d))} (closed on {done_branch()} or recorded assignments), "
              f"{sum(1 for i, d in g.live.items() if i in g.dist1 and unfolded(d) and not finished(d) and not is_leaf(d))} split and reviewed")
        if only_stage1:
            print("stages 2 and 3: disabled by the human for this isolated run")
            return 0
        print(f"stage 2 open: {len(s2)} nodes to state; not open: " + ", ".join(f"{v} {k}" for k, v in why.items()) if why else f"stage 2 open: {len(s2)} nodes to state")
        print(f"stage 3 waiting: {len(w)} stated modules whose node depends on a node without a declaration")
    elif cmd == "items":
        for dist, i in s1:
            print(f"1\t{i}\t{dist}\t{audit_state(g.live[i])}")
        for pri, hgt, i, nb in s2:
            print(f"2\t{i}\t{hgt}\t{'target-statement' if pri == 0 else 'state'}\t{nb}")
    elif cmd == "waiting":
        for m, c in w:
            print(f"{m}\t{c}")
    else:
        print(__doc__); return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
