#!/usr/bin/env python3
"""coord/queue-batches.tsv: the batch of each item of coord/queue.tsv (launcher, 2026-10-15; batch 3 and pruning 2026-10-16;
sorry route 2026-10-17; below the route 2026-10-18).
A stage-3 item belongs to an open batch N (coord/batchN-targets.txt without coord/batchN-complete.txt, every N present)
when it is on that batch's sorry route (local/sorry-route.json, tools/sorry_route.py: it has a sorried declaration
that the batch's targets actually use), or below a route sorry of that batch (the human, 2026-10-18; tools/below_route.py:
in the dependency closure of a node whose declaration is a sorry on the batch's own route, within the batch's own
reach), read from local/stage3-reach.json as tools/queue.py write selected the items (computed here when that file is
missing or belongs to another route). A module whose source changed after the route was computed also counts for
every batch whose import closure reaches it, until the next route refresh (a landing may have split off a new sorry).
When the route is missing or a walk failed, the batch falls back to its import closure and this script says so.
The dispatch tag (queue-batches.tsv) is the first such batch; queue-batches-all.tsv lists every one. A stage-3 item
reached by no open batch is tagged `unneeded`, which no dispatcher lane serves; a rework item (kind `rework`, tools/rework.py)
is tagged `rework`, the dispatcher's first lane (the human, 2026-10-20) (tools/queue.py lists only modules on
the route or below it, so this is rare). Other stages: untagged."""
import collections, pathlib, re, sys
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
import sorry_route, below_route
_, imports = li.scan()
route = sorry_route.load()
below = below_route.read_reach(route["t"]) if route else None
if route and below is None:   # queue.py write did not run for this route: compute what it would have selected
    import dag_queue
    below = below_route.reach(dag_queue.Dag(dag_queue.load()), dag_queue)


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
    return route["batches"][f"batch{n}"] | sorry_route.changed_since(route["t"], c, f"batch{n}") | set((below or {}).get(f"batch{n}", ()))


ns = sorted(int(m.group(1)) for p in (R / "coord").glob("batch*-targets.txt") if (m := re.fullmatch(r"batch(\d+)-targets\.txt", p.name)))
rs = [(f"batch{n}", reach(n)) for n in ns]
# Stages 1 and 2 (node ids; retirement of ~/weil-newtargets, 2026-10-19, its tools/tag_batches.py): an item reached from a
# batch-2 target node (coord/new-targets.txt minus coord/nodes-batch3/4/5-targets.txt) is batch2; reached only from the
# batch-3 target nodes batch3; only from batch-4 nodes batch4; only from batch-5 nodes (and no batch-2/3/4 node) batch5;
# reached by none: batch3. A batch's closure does not enter the nodes it assumes (coord/assumed.tsv).
import dag_queue as dq
_read = lambda f: [l.split()[0] for l in (R / f).read_text().splitlines() if l.strip() and not l.startswith("#")] if (R / f).exists() else []
_b3 = set(_read("coord/nodes-batch3-targets.txt")); _b4 = set(_read("coord/nodes-batch4-targets.txt")); _b5 = set(_read("coord/nodes-batch5-targets.txt"))
_b2 = [t for t in _read("coord/new-targets.txt") if t not in _b3 | _b4 | _b5]
_g = dq.Dag(dq.load())
_reach2 = set(_g.batch_reach("batch2", set(_b2) & set(_g.live)))
_reach3 = set(_g.batch_reach("batch3", _b3 & set(_g.live)))
_full4 = set(_g.batch_reach("batch4", _b4 & set(_g.live))); _reach4 = _full4 - _reach3
_full5 = set(_g.batch_reach("batch5", _b5 & set(_g.live))); _reach5 = _full5 - _reach3 - _full4
_nfull = {"batch2": _reach2, "batch3": _reach3, "batch4": _full4, "batch5": _full5}


def node_tag(i):
    return "batch2" if i in _reach2 else "batch4" if i in _reach4 else "batch5" if i in _reach5 else "batch3"


def node_tags_all(i):
    return ",".join(b for b in ("batch2", "batch3", "batch4", "batch5") if i in _nfull[b])


rows = []; allrows = []
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if l.startswith("#") or len(r) < 2: continue
    if len(r) > 4 and r[4] == "retire-first":   # unblocks rework roots (twin collisions): the dispatcher's first lane
        rows.append(f"{r[0]}\tretire-first"); allrows.append(f"{r[0]}\tretire-first"); continue
    if len(r) > 4 and r[4] == "retire":   # coord/rework-retire.tsv: the dispatcher's second lane
        rows.append(f"{r[0]}\tretire"); allrows.append(f"{r[0]}\tretire"); continue
    if len(r) > 4 and r[4] == "rework":   # the human, 2026-10-20: quarantined by the upstream sync; the dispatcher's first lane
        rows.append(f"{r[0]}\trework"); allrows.append(f"{r[0]}\trework"); continue
    b = node_tag(r[0]) if r[1] != "3" else next((name for name, s in rs if r[0] in s), "unneeded")
    rows.append(f"{r[0]}\t{b}")
    allb = ",".join(name for name, s in rs if r[0] in s) if r[1] == "3" else node_tags_all(r[0])
    allrows.append(f"{r[0]}\t{allb or b}")
tmp = R / "coord/.queue-batches.tsv"; tmp.write_text("# item\tbatch\n" + "\n".join(rows) + "\n"); tmp.replace(R / "coord/queue-batches.tsv")
tmp = R / "coord/.queue-batches-all.tsv"; tmp.write_text("# item\tbatches (every open batch whose sorry route has the item or whose route sorry it lies below; queue-batches.tsv has the dispatch tag)\n" + "\n".join(allrows) + "\n"); tmp.replace(R / "coord/queue-batches-all.tsv")
print(len(rows), "items tagged;", sum(1 for x in rows if x.endswith("unneeded")), "unneeded;",
      "reach below a route sorry (modules, items or not): " + ", ".join(f"{b} {len(v)}" for b, v in sorted((below or {}).items())) + ("; " + "; ".join(notes) if notes else ""))
