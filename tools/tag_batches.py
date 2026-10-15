#!/usr/bin/env python3
"""coord/queue-batches.tsv: the batch of each stage-3 item of coord/queue.tsv (launcher, 2026-10-15).
An item reached from the first task's target modules (coord/batch1-targets.txt) is batch1; any other is batch2
(reached only from the new targets added to lean/TargetsCheck.lean)."""
import collections, pathlib, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
_, imports = li.scan()
roots = [l.strip() for l in (R / "coord/batch1-targets.txt").read_text().splitlines() if l.strip() and not l.startswith("#")]
seen, dq = set(roots), collections.deque(roots)
while dq:
    x = dq.popleft()
    for i in imports.get(x, ()):
        if i in imports and i not in seen: seen.add(i); dq.append(i)
rows = []
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if l.startswith("#") or len(r) < 2: continue
    rows.append(f"{r[0]}\t{'batch1' if r[0] in seen or r[1] != '3' else 'batch2'}")
tmp = R / "coord/.queue-batches.tsv"; tmp.write_text("# item\tbatch\n" + "\n".join(rows) + "\n"); tmp.replace(R / "coord/queue-batches.tsv")
print(len(rows), "items tagged")
