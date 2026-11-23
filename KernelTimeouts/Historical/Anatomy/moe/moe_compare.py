#!/usr/bin/env python3
"""Compare two MOE line-oriented snapshots.

The comparer treats the path as the identity of an expression position.  It
reports the first structural difference in preorder and separately compares
stored constant metadata.  Snapshot output is intentionally plain text so it
can be inspected without a JSON or Lean runtime.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Node:
    path: str
    kind: str
    payload: str
    hash: str


def read(path: Path) -> tuple[dict[str, str], dict[str, Node], dict[str, dict[str, str]]]:
    stages: dict[str, str] = {}
    nodes: dict[str, Node] = {}
    consts: dict[str, dict[str, str]] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw.startswith("MOE_"):
            continue
        fields: dict[str, str] = {}
        for item in raw.split()[1:]:
            if "=" in item:
                key, value = item.split("=", 1)
                fields[key] = value
        tag = raw.split(" ", 1)[0]
        if tag == "MOE_STAGE":
            stages[fields.get("stage", "?")] = fields.get("status", "")
        elif tag == "MOE_NODE":
            key = f"{fields.get('stage','?')}:{fields.get('side','?')}:{fields.get('path','?')}"
            nodes[key] = Node(fields.get("path", "?"), fields.get("kind", "?"),
                              fields.get("payload", ""), fields.get("hash", "?"))
        elif tag == "MOE_CONST":
            name = fields.get("name", "?")
            consts[name] = fields
    return stages, nodes, consts


def first_divergence(left: dict[str, Node], right: dict[str, Node]) -> str:
    keys = sorted(set(left) | set(right), key=lambda k: (k.count("/"), k))
    for key in keys:
        l = left.get(key)
        r = right.get(key)
        path = (l or r).path
        if l is None or r is None:
            return f"path={path} kind=missing-left" if l is None else f"path={path} kind=missing-right"
        if l.kind != r.kind:
            return f"path={path} kind=kind left={l.kind} right={r.kind}"
        if l.payload != r.payload:
            detail = "universe" if "level" in l.payload or "level" in r.payload else "payload"
            return f"path={path} kind={detail} left={l.payload} right={r.payload}"
        child_prefix = key + "/"
        has_children = any(k.startswith(child_prefix) for k in set(left) | set(right))
        if l.hash != r.hash and not has_children:
            return f"path={path} kind=structural-hash left={l.hash} right={r.hash}"
    return "none"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    parser.add_argument("--stage", help="restrict comparison to one stage, e.g. S4")
    parser.add_argument("--left-side", help="restrict the left snapshot to a side")
    parser.add_argument("--right-side", help="restrict the right snapshot to a side")
    args = parser.parse_args()
    ls, ln, lc = read(args.left)
    rs, rn, rc = read(args.right)
    if args.stage or args.left_side:
        ln = {k: v for k, v in ln.items()
              if (not args.stage or k.startswith(args.stage + ":"))
              and (not args.left_side or k.split(":", 2)[1] == args.left_side)}
    if args.stage or args.right_side:
        rn = {k: v for k, v in rn.items()
              if (not args.stage or k.startswith(args.stage + ":"))
              and (not args.right_side or k.split(":", 2)[1] == args.right_side)}
    if args.left_side:
        ln = {k.split(":", 1)[0] + ":" + v.path: v for k, v in ln.items()}
    if args.right_side:
        rn = {k.split(":", 1)[0] + ":" + v.path: v for k, v in rn.items()}
    print("MOE_COMPARE schema=S0-S6")
    print(f"stages-left={ls}")
    print(f"stages-right={rs}")
    print(f"first-divergence={first_divergence(ln, rn)}")
    for name in sorted(set(lc) | set(rc)):
        if lc.get(name) != rc.get(name):
            print(f"constant-difference name={name} left={lc.get(name)} right={rc.get(name)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
