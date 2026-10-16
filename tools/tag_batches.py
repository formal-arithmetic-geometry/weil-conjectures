#!/usr/bin/env python3
"""coord/queue-batches.tsv: the batch of each item of coord/queue.tsv (launcher, 2026-10-15; batch 3 and pruning 2026-10-16).
A stage-3 item is tagged with the first batch whose target modules (coord/batch1-targets.txt, batch2-targets.txt,
batch3-targets.txt) import it and whose targets are not yet proved. A batch whose targets are proved has a file
coord/batchN-complete.txt; its import closure is no longer work (stage 3 is top-down: a sorry the proved targets do not
use is not a task). A stage-3 item reached by no open batch is tagged `unneeded`, which no dispatcher lane serves.
Other stages: batch1 (this project's stage 1/2 are not used)."""
import collections, pathlib, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
_, imports = li.scan()
def reach(n):
    if (R / f"coord/batch{n}-complete.txt").exists(): return set()
    p = R / f"coord/batch{n}-targets.txt"
    roots = [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")] if p.exists() else []
    seen, dq = set(roots), collections.deque(roots)
    while dq:
        x = dq.popleft()
        for i in imports.get(x, ()):
            if i in imports and i not in seen: seen.add(i); dq.append(i)
    return seen
rs = [(f"batch{n}", reach(n)) for n in (1, 2, 3, 4)]   # 2026-10-17: batch 4 (Poincare duality)
rows = []
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if l.startswith("#") or len(r) < 2: continue
    b = "untagged" if r[1] != "3" else next((name for name, s in rs if r[0] in s), "unneeded")   # 2026-10-16: never batch1 (complete)
    rows.append(f"{r[0]}\t{b}")
tmp = R / "coord/.queue-batches.tsv"; tmp.write_text("# item\tbatch\n" + "\n".join(rows) + "\n"); tmp.replace(R / "coord/queue-batches.tsv")
print(len(rows), "items tagged;", sum(1 for x in rows if x.endswith("unneeded")), "unneeded")
