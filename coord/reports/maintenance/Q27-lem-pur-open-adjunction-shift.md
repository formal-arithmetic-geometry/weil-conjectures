# Q27 stale stage-1 claim repaired

Item: `lem-pur-open-adjunction-shift`. Maintenance time: 2026-10-22T11:13:59Z.

Q119's accepted re-split merged at 2026-10-22T10:25:36Z in
`e15218aa98dea6c49d803f3ca7883c9fbf4b35c1`. The merge added
`lem-pur-inverse-section-adjunction-gluing` and
`lem-pur-exact-adjunction-unit-shift-descent`, set the live review to pass,
and resolved the stage-1 repair note. That commit still contained the old
stage-1 queue row. Q27 obtained a new claim at 10:25:50Z, fourteen seconds
later. The current queue has no row for this item.

The dispatcher reads held claims from `tools/claim.py held_by`, then
`Group.server()` retains its previous stage when `queue_stage()` returns
None. `Group.work()` starts held stage-1 claims without a live completion
check. Consequently every unchanged sandbox was correctly rejected by
preflight with "the item's node file is unchanged" and another worker
was launched. Failure counts did not cause this condition.

Under `coord/.merge.lock`, maintenance verified the live split, passing
Q119 review, resolved repair note, absent queue row, original Q27 claim,
and absence of a Q27 delivery branch or open return, then released only
that stale claim using `tools/claim.py release`. The release is recorded
in `coord/deliveries.log`. The claim and delivery log were backed up as
`<original path>.maint-Q27-1792666995.bak` before the operation. This note and the tracked
claim deletion are committed; unrelated pending delivery-log changes
are left for their existing owner to commit.

Stage 1 of this item is complete. A future worker must follow a newly
released stage-1 repair note if one appears. The existing Lean theorem
still containing sorry is a later-stage obligation, not a reason to
repeat this accepted split. The worker sandbox remains intact.

Prevention belongs in protected launcher/landing code and was not edited:
reconcile held stage-1 claims against current live completion and repair
state before reusing a cached stage. A completed item absent from the
queue, with no open return or unreviewed delivery, should have its stale
claim released through the normal lifecycle. Queue publication after an
accepted landing should also avoid exposing the already-completed row.
Preserve dispatch of listed unclaimed tasks and released repairs, and
base reconciliation on completion rather than retries. No failure cutoff,
concurrency setting, admission limit, throttle, or pause is involved.
