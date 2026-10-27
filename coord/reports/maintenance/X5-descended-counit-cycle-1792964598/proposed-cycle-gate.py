"""Proposed helper for stage3_delivery.edge_fails; NOT installed in the pipeline."""


def inherited_through_helpers(graph, base_graph, nid, dependency, reaches):
    """Recognize a split of an existing cyclic dependency through new nodes.

    Stop at every baseline vertex. Every exit that can return to nid must
    already be mutually reachable with nid on the baseline. A helper's direct
    dependence on nid, or a cycle entirely among helpers, is still a new cycle.
    """
    if dependency in base_graph:
        return reaches(base_graph, dependency, nid) and reaches(base_graph, nid, dependency)

    helpers, frontier, todo = set(), set(), [dependency]
    while todo:
        vertex = todo.pop()
        if vertex in base_graph:
            frontier.add(vertex)
        elif vertex not in helpers:
            helpers.add(vertex)
            todo.extend(v for v in graph.get(vertex, ()) if isinstance(v, str))

    # Do not turn a direct circular proof into an inherited-cycle exception.
    if nid in frontier:
        return False
    returning = [v for v in frontier if reaches(graph, v, nid)]
    if not returning or not all(
        reaches(base_graph, v, nid) and reaches(base_graph, nid, v) for v in returning
    ):
        return False

    # Contracting helpers must not hide a newly introduced helper-only cycle.
    indegree = dict.fromkeys(helpers, 0)
    for vertex in helpers:
        for other in graph.get(vertex, ()):
            if other in helpers:
                indegree[other] += 1
    todo = [v for v, degree in indegree.items() if degree == 0]
    visited = 0
    while todo:
        vertex = todo.pop()
        visited += 1
        for other in graph.get(vertex, ()):
            if other in helpers:
                indegree[other] -= 1
                if indegree[other] == 0:
                    todo.append(other)
    return visited == len(helpers)
