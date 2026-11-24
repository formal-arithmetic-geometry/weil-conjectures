#!/usr/bin/env python3
"""Summarize one READY4.2 MDA root without treating sampled calls as totals."""

import argparse
import collections
import gzip
import json
from pathlib import Path


def rows(path, root):
    opener = gzip.open if str(path).endswith(".gz") else Path(path).open
    with opener(path, "rt", encoding="utf-8") if opener is gzip.open else opener(encoding="utf-8") as stream:
        for line in stream:
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if row.get("root") == root:
                yield row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("events")
    parser.add_argument("--root", required=True, type=int)
    parser.add_argument("--case", required=True)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()
    events = list(rows(args.events, args.root))
    coverage = next((r for r in events if r.get("event") == "coverage"), None)
    if coverage is None:
        parser.error(f"root {args.root} has no complete coverage record")
    groups = [r for r in events if r.get("event") == "mda_group"]
    tops = [r for r in events if r.get("event") == "mda_top"]
    labels = collections.Counter()
    label_time = collections.Counter()
    for row in events:
        if row.get("event") == "aggregate":
            labels[row["provenance"]] += int(row["calls"])
            label_time[row["provenance"]] += int(row["exclusive_ns"])
    assert sum(int(r["calls"]) for r in groups) == int(coverage["total_calls"])
    assert sum(int(r["exclusive_ns"]) for r in groups) == int(coverage["root_exclusive_ns"])
    assert sum(labels.values()) == int(coverage["total_calls"])
    assert sum(int(r["m1_calls"]) for r in groups) == labels["M1"]
    assert sum(int(r["m1_exclusive_ns"]) for r in groups) == label_time["M1"]
    transitions = [r for r in events if r.get("event") == "transition"]
    assert sum(int(r["calls"]) for r in transitions) == int(coverage["total_calls"]) - 1
    print(f"# {args.case} MDA validation")
    print()
    print(f"Root {args.root}: {coverage['total_calls']:,} calls; "
          f"{coverage['root_exclusive_ns'] / 1e6:,.3f} ms comparison-exclusive; "
          f"labels {dict(labels)}. All group and transition sums reconcile.")
    print()
    print("## 4.1 Gateway-to-cost")
    print()
    print("| Gateway ID | Parent | Branch/component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |")
    print("| --- | ---: | --- | --- | --- | ---: | ---: | --- |")
    for row in sorted(tops, key=lambda r: int(r["subtree_exclusive_ns"]), reverse=True)[:args.top]:
        pair = f"`{row['left']}` / `{row['right']}`; Expr in JSONL"
        source = row.get("source", "unknown")
        print(f"| {args.root}:{row['call']} | {row['parent']} | {row['branch']}/{row['component']} | "
              f"{pair} | `{source}` | {row['subtree_m1_calls']:,} | "
              f"{row['subtree_exclusive_ns'] / 1e6:,.3f} | trace; nested rows overlap |")
    print()
    print("## 4.2 Definition/API path")
    print()
    print("| Candidate definition/API | Role | First seen at | Kernel path | M1 calls | M1 exclusive ms | Intervention | Evidence |")
    print("| --- | --- | --- | --- | ---: | ---: | --- | --- |")
    for row in sorted(groups, key=lambda r: int(r["m1_exclusive_ns"]), reverse=True)[:args.top]:
        print(f"| `{row['source']}` / {row['component']} | gateway/component candidate | aggregate | "
              f"{row['gateway']} | {row['m1_calls']:,} | {row['m1_exclusive_ns'] / 1e6:,.3f} | "
              "not tested in Batch 0 | aggregate, attribution provisional |")
    print()
    print("Direct group times partition the root. Inclusive subtree times overlap; do not add them.")


if __name__ == "__main__":
    main()
