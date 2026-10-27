# Retired stale N9 stage-1 handoff

The return for sk-thm-groth-ss at 83112f5072d86c6b45e725b98f1b71d94f573880
asked for a side-to-live promotion that cannot repair this assignment. The
separate newtargets repository was retired on 2026-10-19. Both queue and
landing now read this repository's dag/nodes.

The actual landing rejection is membership in Dag.stage1(): this item is
outside the current stage-1 reach. Its trace-formula route is cut at
sk-thm-trace-transport, assumed by batch 5 in coord/assumed.tsv under the
human's 2026-10-18 decision. No current queue or preopen record lists it.
Removing the item's generated lean_audit still leaves it outside stage 1.
The stale return and N9 claim, rather than eligible queue work, caused the
dispatcher to keep assigning it. This is scope retirement, not a proof
completion, abandonment, throttle, or pause.

The obsolete return and its N9 claim are removed, with adjacent .bak copies.
The delivery remains at the refs/superseded archive in evidence.json.
review.md and reviewer-node.json preserve the independent FIX verdict and
its ten-step proof, including scheme-to-site step 9 that repeated worker
pushes kept dropping. They are historical review material, not a new landing.

If a future target genuinely reopens the node, start from that fixed proof,
revalidate current dependencies and realization fields, refresh citations,
and submit it for current independent review. Do not infer a full attachment
from the generated audit's closed state: the abstract Lean declaration alone
does not establish every site/module specialization in this item's statement.

Protected tool defect, not changed here: tools/nt_land_batch.py's notopen
branch calls an incomplete queued node a side completion without testing
either differing DAG paths or a completed local node. It must distinguish
pruned work from a real copy mismatch and retire stale coordination records
when the same current reachability policy proves them obsolete. Preserve
released repair notes, genuinely reopened nodes, stage-2 claims, moved heads,
and delivery history. The automatic return must not ask workers to rebase
unchanged mathematics to repair a maintainer-side eligibility decision.
