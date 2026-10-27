# Maintenance: lem-sfb-flat-geometrically-reduced-pullback (NC)

The repeated stage-1 failures came from an obsolete NC claim, not an unfinished
node. NJ delivered 58511146544; L independently reviewed the Mathlib match and
landed it in ed4485354a3a71dea5a10dfb4cabea0c9b1fb69d at
2026-10-22T03:11:06Z. NC claimed the item at 03:11:27Z, after that landing.
The claim survived the queue refresh and was later committed by a build.

The live node has status `mathlib`, reviewed result `pass` by L /
NT-cc-NJ-585111465, and `dag_queue.stage1_completed` and
`claim.node_finished(item, "1")` both return true. The current queue contains no
row for this item; NC has no delivery branch, open return, or released repair
note for it. Each NC dry run rejects the byte-identical node with exactly
"the item's node file is unchanged". This is the correct delivery diagnostic.

Closed the obsolete claim with `tools/claim.py done NC`, preserving a `.bak`
of the claim and delivery log. Committed the claim deletion, only this
maintenance's delivery-log entry, and this record under `coord/.merge.lock`
with `SHEAF_LEAD=L-only` and the required Bin Wu identity. Existing uncommitted
delivery-log entries were left for their owners.

The launcher owner should add stage-aware completion reconciliation to
`/home/ubuntu/weil-launcher-all/dispatch_all.py`, `Group.work`: held stage-1
items are relaunched without checking live completion, whereas stage 3 has a
completion check. Reconcile both held/pending work against the live queue and
node before launching, preserving explicit returns and released repair notes.
Do not impose retry limits, backoff, or concurrency restrictions. The protected
launcher source was not changed by this maintenance.

No stage-1 work remains on this item. A future worker must use the current live
record; do not manufacture a split or metadata-only delivery of the reviewed
Mathlib leaf. No Lean source was changed and no compiler was needed. Existing
sandbox evidence and running processes were left intact.
