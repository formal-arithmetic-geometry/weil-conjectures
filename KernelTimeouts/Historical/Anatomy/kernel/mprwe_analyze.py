#!/usr/bin/env python3
"""Summarize bounded READY3 MPRWE JSONL events.

The kernel deliberately records raw events only.  This pass applies a
conservative structural heuristic and reports ambiguous nodes separately.
Semantic provenance still requires review of the selected expressions.
"""
import argparse
import collections
import json
import sys


LABELS = ("M0", "M1", "M2", "Matched", "Unclassified")


def load(path):
    events = []
    with open(path, encoding="utf-8") as stream:
        for line in stream:
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return events


def classify(events, root=None):
    enters = {(e["root"], e["call"]): e for e in events if e.get("event") == "enter"}
    exits = {(e["root"], e["call"]): e for e in events if e.get("event") == "exit"}
    reductions = collections.defaultdict(list)
    for e in events:
        if e.get("event") == "reduction":
            reductions[(e["root"], e["call"])].append(e)
    if root is None:
        root = max(collections.Counter(e.get("root") for e in events).items(),
                   key=lambda pair: pair[1])[0]
    calls = {call: e for (event_root, call), e in enters.items() if event_root == root}
    labels = {}
    for call, entry in sorted(calls.items()):
        parent = entry.get("parent", 0)
        parent_key = (root, parent)
        if call == 1 or not parent:
            labels[call] = "M0"
            continue
        left, right = entry.get("left"), entry.get("right")
        if left == right:
            labels[call] = "Matched"
        elif reductions.get(parent_key):
            changed = any(r.get("before_left") != r.get("after_left") or
                          r.get("before_right") != r.get("after_right")
                          for r in reductions[parent_key])
            labels[call] = "M2" if changed else "Unclassified"
        else:
            # A distinct head below a mismatched parent may be inherited M1,
            # or an independent M2.  Without expression/context identity it
            # is intentionally left unresolved.
            labels[call] = "Unclassified"
    totals = {label: {"calls": 0, "exclusive_ns": 0} for label in LABELS}
    for call, label in labels.items():
        totals[label]["calls"] += 1
        totals[label]["exclusive_ns"] += exits.get(call, {}).get("exclusive_ns", 0)
    top = []
    for call, label in labels.items():
        event = exits.get((root, call))
        if event:
            top.append((event.get("exclusive_ns", 0), call, label,
                        calls[call].get("left"), calls[call].get("right"),
                        calls[call].get("depth")))
    top.sort(reverse=True)
    return root, totals, top[:20], len(calls), len(exits), len(reductions)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("events")
    parser.add_argument("--root", type=int)
    args = parser.parse_args()
    events = load(args.events)
    if not events:
        raise SystemExit("no valid events")
    root, totals, top, entered, exited, reductions = classify(events, args.root)
    print("root=%s entered=%d exited=%d reductions=%d" %
          (root, entered, exited, reductions))
    for label in LABELS:
        row = totals[label]
        print("%s calls=%d exclusive_ms=%.3f" %
              (label, row["calls"], row["exclusive_ns"] / 1e6))
    print("top_exclusive:")
    for ns, call, label, left, right, depth in top:
        print("call=%d label=%s depth=%s exclusive_ms=%.3f left=%s right=%s" %
              (call, label, depth, ns / 1e6, left, right))


if __name__ == "__main__":
    main()
