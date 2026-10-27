# Q84 stale claim repair — 2026-10-23

Item: `lem-pur-adic-projection-shift-coherence`, stage 1.

Q138's accepted re-split landed at 2026-10-22T09:38:28Z, commit
`01257b113c8`, independent reviewer `NT-cc-Q138-d0d38102b` (PASS).
It extracted `lem-pur-open-system-tensor-shift` and
`lem-pur-strict-compactification-projection-shift` and resolved the human's
stage-1 repair note. The node also already has its accepted stage-2 record
from NH (`2fce3087773`). There is no outstanding stage-1 work on the parent.

Q84 acquired a new claim at 2026-10-22T09:38:34Z, six seconds after landing,
from a queue snapshot that still listed the item. `tools/claim.py take`
intentionally permits any listed item (the human's 2026-10-22 decision).
After queue regeneration removed it, the held claim survived. The dispatcher's
`Group.server()` received `queue_stage(item) is None` and retained the cached
stage 1; `Group.work()` checks completed off-queue work only for stage 3.
It consequently relaunched Q84 repeatedly, although each worker correctly
followed the live-wins rule and reported BLOCKED. There are 69 preserved Q84
run directories with this same final answer; dispatcher state counted 64.
This is a stale claim/reconciliation failure, not a mathematical or provider
failure. The claim TTL is 72 hours, so expiry had not removed it.

Repair: backed up Q84's claim and `coord/deliveries.log` with suffix
`.maint-Q84-1792740154.bak`, rechecked completion and the absence of an open
Q84 return/delivery, and released this off-queue claim through
`tools/claim.py release`. No node, proof, Lean module, review, resolved repair
note, queue row, failure counter, or dispatcher code was changed.

Verification: the live predicates say stage 1 complete, stage 2 complete,
repair resolved, queue stage absent. Before repair, `take-many --with-stage
Q84 <item> 1` refused a fresh claim as already completed. After repair,
Q84 no longer holds the item, its claim file is absent, and node/repair-note
SHA-256 digests are unchanged. No Lean file changed, so no compile was needed.

Launcher follow-up (protected file; not edited): reconcile held stage-1/2
claims that are absent from the current live queue in `dispatch_all.py`
`Group.server()` / `Group.work()`. Ask the server's stage-aware completion
predicate and repair state before relaunching. With no open return/delivery,
release a completed off-queue claim instead of falling back to a cached stage.
Preserve explicitly released repairs and all listed tasks. Failed/empty queue
reads and missing nodes must not be treated as evidence of completion. This
is completion reconciliation and does not use a failure-count threshold or
introduce a concurrency limit, throttle, admission rule, or pause.

The next worker must not re-split this parent or fabricate a new repair order.
A future explicit repair note may legitimately reopen it; otherwise its
accepted stage-1 and stage-2 records stand. Its new child nodes are independent
queue items, not work to do under this stale parent assignment.
