#!/usr/bin/env python3
"""coord/queue-batches.tsv: the batch of each item of coord/queue.tsv (launcher, 2026-10-15; batch 3 and pruning 2026-10-16;
sorry route 2026-10-17).
A stage-3 item belongs to an open batch N (coord/batchN-targets.txt without coord/batchN-complete.txt, every N present)
when it is on that batch's sorry route (local/sorry-route.json, tools/sorry_route.py): it has a sorried declaration
that the batch's targets actually use. A module whose source changed after the route was computed also counts for
every batch whose import closure reaches it, until the next route refresh (a landing may have split off a new sorry).
When the route is missing or a walk failed, the batch falls back to its import closure and this script says so.
The dispatch tag (queue-batches.tsv) is the first such batch; queue-batches-all.tsv lists every one. A stage-3 item
reached by no open batch is tagged `unneeded`, which no dispatcher lane serves (tools/queue.py no longer lists modules
off the route, so this is rare). Other stages: untagged."""
import collections, pathlib, re, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
import sorry_route
_, imports = li.scan()
route = sorry_route.load()


def closure(n):
    p = R / f"coord/batch{n}-targets.txt"
    roots = [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")] if p.exists() else []
    seen, dq = set(roots), collections.deque(roots)
    while dq:
        x = dq.popleft()
        for i in imports.get(x, ()):
            if i in imports and i not in seen: seen.add(i); dq.append(i)
    return seen


notes = []
def reach(n):
    if (R / f"coord/batch{n}-complete.txt").exists(): return set()
    c = closure(n)
    if route is None or f"batch{n}" not in route["batches"]:
        notes.append(f"batch{n}: no complete sorry route, import closure used"); return c
    return route["batches"][f"batch{n}"] | sorry_route.changed_since(route["t"], c)


ns = sorted(int(m.group(1)) for p in (R / "coord").glob("batch*-targets.txt") if (m := re.fullmatch(r"batch(\d+)-targets\.txt", p.name)))
rs = [(f"batch{n}", reach(n)) for n in ns]
rows = []; allrows = []
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if l.startswith("#") or len(r) < 2: continue
    b = "untagged" if r[1] != "3" else next((name for name, s in rs if r[0] in s), "unneeded")
    rows.append(f"{r[0]}\t{b}")
    allb = ",".join(name for name, s in rs if r[0] in s) if r[1] == "3" else ""
    allrows.append(f"{r[0]}\t{allb or b}")
tmp = R / "coord/.queue-batches.tsv"; tmp.write_text("# item\tbatch\n" + "\n".join(rows) + "\n"); tmp.replace(R / "coord/queue-batches.tsv")
tmp = R / "coord/.queue-batches-all.tsv"; tmp.write_text("# item\tbatches (every open batch whose sorry route has the item; queue-batches.tsv has the dispatch tag)\n" + "\n".join(allrows) + "\n"); tmp.replace(R / "coord/queue-batches-all.tsv")
print(len(rows), "items tagged;", sum(1 for x in rows if x.endswith("unneeded")), "unneeded" + ("; " + "; ".join(notes) if notes else ""))
