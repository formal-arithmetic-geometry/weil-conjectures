"""Stage-2 target skips and runtime waits for genuine unstated DAG dependencies."""
import json
import pathlib
import sys
import leanindex as li


WAIT_FILE = li.ROOT / "local/stage2/dependency-waits.json"


def waits():
    if not WAIT_FILE.exists():
        return {}
    return json.loads(WAIT_FILE.read_text())


def missing(graph, dependencies):
    return [d for d in dependencies if d in graph.live and not graph.stated(d)]


def frontier(graph, dependencies):
    """Ready prerequisites first, including nodes absent from the ordinary target route."""
    ready, seen = [], set()
    def visit(nid):
        nid = graph.resolve(nid)
        if nid in seen or nid not in graph.live or graph.stated(nid):
            return
        seen.add(nid)
        deps = missing(graph, graph.deps(nid, "stmt"))
        if deps:
            for dep in deps:
                visit(dep)
        else:
            # human, 2026-10-16 (STAGE 1 -> 2 HANDOFF): only a split prerequisite is offered for its statement
            import dag_queue
            if dag_queue.unfolded(graph.live[nid]):
                ready.append(nid)
    for dep in dependencies:
        visit(dep)
    return ready


def wait_cycle(graph, state, item, dependencies):
    """Return a proposed cycle, including runtime edges omitted from stmt_deps."""
    def path(nid, seen):
        if nid == item:
            return [nid]
        if nid in seen or nid not in graph.live or graph.stated(nid):
            return None
        for dep in dict.fromkeys([*graph.deps(nid, "stmt"), *state.get(nid, [])]):
            found = path(graph.resolve(dep), seen | {nid})
            if found:
                return [nid, *found]
        return None
    for dep in dependencies:
        found = path(dep, set())
        if found:
            return [item, *found]
    return []


def eligible(graph, items, why):
    pending = {item: missing(graph, deps) for item, deps in waits().items()}
    pending = {item: deps for item, deps in pending.items() if deps}
    priority = list(dict.fromkeys(n for deps in pending.values() for n in frontier(graph, deps)))
    s1open = {nid for _, nid in graph.stage1()}   # 2026-10-16: a stage-1 item is not listed again for stage 2
    priority = [n for n in priority if n not in s1open]
    rows = {row[2]: row for row in items}
    for nid in priority:
        rows.setdefault(nid, (0, graph.h(nid), nid, 0))
    # human, 2026-10-16: no dispatch restrictions. A reported wait only puts the missing prerequisites first;
    # the waiting item stays a task, and no target is deferred.
    items = [rows[nid] for nid in priority] + [row for row in items if row[2] not in priority]
    return items, why
    roots = set()
    if not roots:
        return items, why
    deferred = set(graph.distances_from(roots)) - set(graph.distances_from(set(graph.targets) - roots))
    allowed = []
    for row in items:
        nid = row[2]
        if nid in deferred:
            why["waits for an explicitly deferred target"] += 1
        else:
            allowed.append(row)
    return allowed, why


def main():
    # Local runtime state, serialized with queue/landing writers; never a DAG edit.
    from mergelock import merge_lock
    import dag_queue
    import nt_merge2
    item, *deps = sys.argv[1:]
    with merge_lock():
        graph = dag_queue.Dag(dag_queue.load())
        resolved = [graph.resolve(d) for d in deps]
        if any(d not in graph.live for d in resolved) or item in resolved:
            raise SystemExit("Refused: wait must name other existing DAG nodes")
        state = waits()
        outstanding = missing(graph, resolved)
        cycle = wait_cycle(graph, state, item, outstanding)
        if cycle:
            print(json.dumps({"missing": [], "ready": [], "cycle": cycle}))
            return
        if outstanding:
            state[item] = outstanding
        else:
            state.pop(item, None)
        WAIT_FILE.parent.mkdir(parents=True, exist_ok=True)
        tmp = WAIT_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(state, indent=2) + "\n")
        tmp.replace(WAIT_FILE)
        nt_merge2.md.refresh_queue("stage 2 dependency wait")
        print(json.dumps({"missing": outstanding, "ready": frontier(graph, outstanding)}))


if __name__ == "__main__":
    main()
