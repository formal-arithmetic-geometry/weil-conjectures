#!/usr/bin/env python3
"""coord/queue-batches.tsv: the batch of each item of coord/queue.tsv (launcher, 2026-10-15; batch 3 2026-10-16).
A stage-3 item reached from the first task's target modules (coord/batch1-targets.txt) is batch1; else one reached from
the batch-2 target modules (coord/batch2-targets.txt) is batch2; any other stage-3 item is batch3. Other stages: batch1."""
import collections, pathlib, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
_, imports = li.scan()
def reach(f):
    p = R / f
    roots = [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")] if p.exists() else []
    seen, dq = set(roots), collections.deque(roots)
    while dq:
        x = dq.popleft()
        for i in imports.get(x, ()):
            if i in imports and i not in seen: seen.add(i); dq.append(i)
    return seen
r1, r2 = reach("coord/batch1-targets.txt"), reach("coord/batch2-targets.txt")
rows = []
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if l.startswith("#") or len(r) < 2: continue
    b = "batch1" if r[0] in r1 or r[1] != "3" else "batch2" if r[0] in r2 else "batch3"
    rows.append(f"{r[0]}\t{b}")
tmp = R / "coord/.queue-batches.tsv"; tmp.write_text("# item\tbatch\n" + "\n".join(rows) + "\n"); tmp.replace(R / "coord/queue-batches.tsv")
print(len(rows), "items tagged")
