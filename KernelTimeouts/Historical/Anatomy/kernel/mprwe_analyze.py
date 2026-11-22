#!/usr/bin/env python3
"""Analyze READY3.1 MPRWE events.

Raw enter/exit records are bounded. The kernel emits aggregate records for
every call, grouped by provenance and path, so exclusive totals remain
complete. Raw records retain hashes and paths for review.
"""
import argparse
import collections
import json


LABELS = ("M0", "M1", "M2", "Matched", "Unclassified")


def load(path):
    events = []
    with open(path, encoding="utf-8") as stream:
        for line in stream:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(event, dict):
                events.append(event)
    return events


def _root_ids(events):
    return [e["root"] for e in events if isinstance(e.get("root"), int)]


def _label(entry, parent):
    recorded = entry.get("provenance")
    if recorded in LABELS:
        return recorded
    if not parent:
        return "M0"
    if entry.get("left_hash") is not None and entry.get("left_hash") == entry.get("right_hash"):
        return "Matched"
    child_l = entry.get("div_left_hash")
    child_r = entry.get("div_right_hash")
    parent_l = entry.get("parent_div_left_hash")
    parent_r = entry.get("parent_div_right_hash")
    if child_l and child_r and parent_l and parent_r and child_l == parent_l and child_r == parent_r:
        return "M1"
    if entry.get("reduction_exposed") or entry.get("phase") == "reduction-exposed":
        return "M2"
    return "Unclassified"


def classify(events, root=None):
    roots = _root_ids(events)
    if not roots:
        raise ValueError("events contain no numeric root")
    coverage = {e["root"]: e for e in events if e.get("event") == "coverage" and isinstance(e.get("root"), int)}
    aggregates = [e for e in events if e.get("event") == "aggregate" and e.get("provenance") in LABELS]
    if root is None:
        candidates = collections.Counter()
        for event in coverage.values():
            candidates[event["root"]] += int(event.get("total_calls", 0))
        for event in aggregates:
            candidates[event["root"]] += int(event.get("calls", 0))
        if not candidates:
            candidates.update(roots)
        root = candidates.most_common(1)[0][0]

    enters = {(e["root"], e["call"]): e for e in events
              if e.get("event") == "enter" and isinstance(e.get("root"), int) and isinstance(e.get("call"), int)}
    exits = {(e["root"], e["call"]): e for e in events
             if e.get("event") == "exit" and isinstance(e.get("root"), int) and isinstance(e.get("call"), int)}
    reductions = collections.defaultdict(list)
    for event in events:
        if event.get("event") == "reduction" and event.get("root") == root:
            reductions[(event.get("root"), event.get("call"))].append(event)

    calls = {call: event for (event_root, call), event in enters.items() if event_root == root}
    labels = {}
    for call, entry in sorted(calls.items()):
        parent_id = entry.get("parent", 0)
        labels[call] = _label(entry, enters.get((root, parent_id)))

    totals = {label: {"calls": 0, "exclusive_ns": 0, "reduction_ns": 0} for label in LABELS}
    aggregate_rows = [event for event in aggregates if event.get("root") == root]
    if aggregate_rows:
        for event in aggregate_rows:
            row = totals[event["provenance"]]
            row["calls"] += int(event.get("calls", 0))
            row["exclusive_ns"] += int(event.get("exclusive_ns", 0))
            row["reduction_ns"] += int(event.get("reduction_ns", 0))
    else:
        for call, label in labels.items():
            event = exits.get((root, call), {})
            totals[label]["calls"] += 1
            totals[label]["exclusive_ns"] += int(event.get("exclusive_ns", 0))
            totals[label]["reduction_ns"] += int(event.get("reduction_ns", 0))

    top = []
    for call, label in labels.items():
        event = exits.get((root, call))
        if event:
            top.append((int(event.get("exclusive_ns", 0)), call, label,
                        calls[call].get("left"), calls[call].get("right"),
                        calls[call].get("depth"), calls[call].get("div_path", "")))
    top.sort(reverse=True)
    coverage_row = coverage.get(root, {})
    total_calls = int(coverage_row.get("total_calls", sum(row["calls"] for row in totals.values())))
    root_exclusive = int(coverage_row.get("root_exclusive_ns", sum(row["exclusive_ns"] for row in totals.values())))
    traced_calls = int(coverage_row.get("traced_calls", sum(int(e.get("traced_calls", 0)) for e in aggregate_rows)))
    traced_exclusive = int(coverage_row.get("traced_exclusive_ns", sum(int(e.get("traced_exclusive_ns", 0)) for e in aggregate_rows)))
    return {
        "root": root,
        "totals": totals,
        "top": top[:10],
        "entered": len(calls),
        "exited": sum(1 for key in exits if key[0] == root),
        "reductions": sum(len(value) for key, value in reductions.items() if key[0] == root),
        "total_calls": total_calls,
        "root_exclusive_ns": root_exclusive,
        "traced_calls": traced_calls,
        "traced_exclusive_ns": traced_exclusive,
        "aggregate": bool(aggregate_rows),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("events")
    parser.add_argument("--root", type=int)
    args = parser.parse_args()
    result = classify(load(args.events), args.root)
    print("root=%s entered=%d exited=%d reductions=%d aggregate=%s" %
          (result["root"], result["entered"], result["exited"], result["reductions"], result["aggregate"]))
    print("coverage traced_calls=%d total_calls=%d traced_share=%.3f traced_exclusive_ms=%.3f root_exclusive_ms=%.3f" %
          (result["traced_calls"], result["total_calls"],
           result["traced_calls"] / result["total_calls"] if result["total_calls"] else 0,
           result["traced_exclusive_ns"] / 1e6, result["root_exclusive_ns"] / 1e6))
    for label in LABELS:
        row = result["totals"][label]
        print("%s calls=%d exclusive_ms=%.3f reduction_ms=%.3f share=%.3f" %
              (label, row["calls"], row["exclusive_ns"] / 1e6, row["reduction_ns"] / 1e6,
               row["exclusive_ns"] / result["root_exclusive_ns"] if result["root_exclusive_ns"] else 0))
    print("top_exclusive:")
    for ns, call, label, left, right, depth, path in result["top"]:
        print("call=%d label=%s depth=%s exclusive_ms=%.3f path=%s left=%s right=%s" %
              (call, label, depth, ns / 1e6, path, left, right))


if __name__ == "__main__":
    main()
