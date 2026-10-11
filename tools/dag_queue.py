#!/usr/bin/env python3
"""The items of stages 1 and 2, read from the DAG, and the modules that stage 3 must still wait for.

Usage:
  tools/dag_queue.py summary      how many nodes each stage has open, and why the others are not open
  tools/dag_queue.py items        the open items, one per line: stage, item, distance (to a target in stage 1, to Mathlib in stage 2),
                                  kind (in stage 1 the node's lean_audit state on the done branch), in stage 2 also blockers
  tools/dag_queue.py waiting      modules whose proof uses a node that has no Lean declaration yet, one per line

`queue.py write` calls this and puts the items into coord/queue.tsv; run this by hand only to look.

What is open follows the stage documents. A node that no target reaches is not open for any stage. A node is open for

  stage 1  (SETUP.md, requirements of 2026-10-09) when a target reaches it without passing through a finished
           node, and it is neither finished, nor a Mathlib leaf, nor split. A node is finished when its
           `lean_audit` state on the branch SHEAF_DONE_BRANCH (default slopmaster2) is `closed`: its Lean exists
           and no `sorry` is reachable from it, and nothing below it is an item. A node is split only when a
           worker has checked it against stages/1-dag.md (`status` is `split`) and the lead has reviewed that
           (`reviewed` is set); the `imported` status of the blueprint import does not count. Every other
           reached node (states none, sorry_here, rests_on_sorry, closed_part) is an item, nearest to a
           target first, the distance counted through unfinished nodes only; since 2026-10-09 the order is first the rank of the
           node's unit on the targets' unit route (tools/units.py route; units outside the route last), then the distance
           (the key printed by `items` is rank*1000 + distance);
  stage 2  when stage 1 has split it (a definition naming the notions it is built from, or a statement with its proof in steps),
           it has no Lean declaration yet, and every node its statement needs has one or is a Mathlib leaf;
           definitions before statements (launcher, 2026-10-11); then, blockers first (human, 2026-10-11 23:30 +08), the
           item that the most stage-2 nodes still needing a statement wait for, counted transitively through stmt_deps
           (`items` prints the count last, queue.tsv as the column `blockers`); ties nearest to Mathlib first (the
           fewest dependency steps down to a Mathlib leaf), so that the statements climb from Mathlib upward. With SHEAF_EARLY_REVIEW=1 in coord/sheaf.env the nodes
           needed to state the targets come first instead.

A module of stage 3 is held back ("waiting") while a node that its proof uses has no Lean declaration: its
proof cannot be written yet. The order of the dependencies is never overridden: no node is stated before the
nodes its statement needs, so stage 2 climbs from Mathlib upward whatever order stage 1 or stage 3 keep.

The DAG layout is the project's own (`stages/1-dag.md` §1 fixes the content, not the field names). The FIELDS
table below lists the names this script accepts for each piece of content; the maintainer adapts it to the
project's layout, as `tools/README.md` says. `SHEAF_DAG` in coord/sheaf.env names the node directory when it is
not `dag/nodes`.
"""
from __future__ import annotations
import collections, json, pathlib, sys

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
            return str(b["state"])
    return "none"


def finished(d) -> bool:
    """Stage 1 is finished with the node: its Lean on the done branch is closed (SETUP.md). Nothing below it is an item."""
    return audit_state(d) in DONE_STATES


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
    return str(field(d, "status") or "").lower() == "split" and bool(field(d, "reviewed"))


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
        self.n = nodes
        self.merged = {i: str(field(d, "merged")) for i, d in nodes.items()
                       if field(d, "merged") or str(field(d, "status") or "").lower() == "merged"}
        self.live = {i: d for i, d in nodes.items() if i not in self.merged}
        self.targets = [i for i, d in self.live.items() if field(d, "target") or str(field(d, "kind") or "").lower() == "target"]
        self.dist = self.distances(cut=False)    # every node a target reaches: the DAG check and stages 2 and 3
        self.dist1 = self.distances(cut=True)    # reached without passing through a finished node: stage 1
        self.height = {}   # fewest dependency steps down to a Mathlib leaf

    def distances(self, cut: bool) -> dict[str, int]:
        return self.distances_from(self.targets, cut)

    def distances_from(self, roots, cut: bool = False) -> dict[str, int]:
        dist = {}
        dq = collections.deque((t, 0) for t in roots)
        while dq:
            i, k = dq.popleft()
            if i in dist:
                continue
            dist[i] = k
            if cut and finished(self.live[i]):
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
        return d is None or is_leaf(d) or has_decl(d)   # a dependency on a missing node is reported by the DAG check, not here

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
        return sorted(((rank.get(self.live[i].get("unit"), big) if rank else 0) * 1000 + self.dist1[i], i)
                      for i, d in self.live.items() if i in self.dist1 and not unfolded(d))

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
        """A stage-2 node that still needs a statement: reached from a target, not a Mathlib leaf, no Lean declaration."""
        d = self.live.get(i)
        return d is not None and i in self.dist and not is_leaf(d) and not has_decl(d)

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
        early = li.config().get("SHEAF_EARLY_REVIEW", "") not in ("", "0", "no")
        for i, d in self.live.items():
            if i not in self.dist or is_leaf(d) or has_decl(d):
                continue
            if not unfolded(d):
                why["waits for stage 1"] += 1; continue
            if not all(self.stated(c) for c in self.deps(i, "stmt")):
                why["waits for a statement dependency"] += 1; continue
            items.append((0 if early and i in tsc else 1, self.h(i), i))
        # launcher, 2026-10-11 10:50 UTC (STAGE 2 ORDER: DEFINITIONS FIRST): a statement cannot be written before its
        # definitions, so within the open items the definitions come first, then the statements, each by the order above.
        # human, 2026-10-11 23:30 +08 (STAGE 2 ORDER: BLOCKERS FIRST): after the definitions rule, the item that the most
        # stage-2 nodes wait for (transitively through stmt_deps) comes first; ties by the distance order above
        b = self.blockers([t[2] for t in items])
        items = [(pri, hgt, i, b[i]) for pri, hgt, i in items]
        return sorted(items, key=lambda t: (t[0], not is_def(self.live[t[2]]), -t[3], t[1], t[2])), why

    def waiting(self) -> list[tuple[str, str]]:
        """(module, node it waits for) for every stated node whose proof uses an unstated node."""
        out = []
        for i, d in self.live.items():
            if is_leaf(d) or not has_decl(d) or not module_of(d):
                continue
            for c in self.deps(i, "proof"):
                if not self.stated(c):
                    out.append((module_of(d), c)); break
        return sorted(out)


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "summary"
    if not nodes_dir().is_dir():
        raise SystemExit(f"no DAG at {nodes_dir()}")
    g = Dag(load())
    s1 = g.stage1(); s2, why = g.stage2(); w = g.waiting()
    if cmd == "summary":
        print(f"nodes: {len(g.n)} ({len(g.merged)} merged, {sum(1 for d in g.live.values() if is_leaf(d))} Mathlib leaves, "
              f"{len(g.targets)} targets, {sum(1 for i in g.live if i not in g.dist)} not reached from a target)")
        print(f"stage 1 open: {len(s1)} nodes to split (" + ", ".join(f"{v} {k}" for k, v in sorted(g.stage1_states().items()))
              + f"); finished: {sum(1 for d in g.live.values() if finished(d))} closed on {done_branch()}, "
              f"{sum(1 for i, d in g.live.items() if i in g.dist1 and unfolded(d) and not finished(d) and not is_leaf(d))} split and reviewed")
        print(f"stage 2 open: {len(s2)} nodes to state; not open: " + ", ".join(f"{v} {k}" for k, v in why.items()) if why else f"stage 2 open: {len(s2)} nodes to state")
        print(f"stage 3 waiting: {len(w)} stated modules whose proof uses a node without a declaration")
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
