# Q08 Weil cohomology stale claim reconciliation (2026-10-22)

The item `lem-pod-weil-cohomology-base-change-frobenius-power` was delivered
by Q13 and independently reviewed PASS by `NT-cc-Q13-6e4d428b6` in commit
`fc333cf6f0e`. `coord/deliveries.log` records completion at 04:20:15 UTC.
Q08 claimed the same item at 04:20:39 UTC from a stale stage-1 queue entry.
The reviewed split has since left `coord/queue.tsv`, but its Q08 claim
survived. The dispatcher falls back to its remembered stage 1 when the
server reports queue stage `-`, restarting completed work indefinitely.

Workers alternated between BLOCKED (the unchanged-item preflight refusal
and live-wins rule) and ATTACH (the historical sorried Lean declaration),
which independent attachment checks rejected. These are consequences of
the stale assignment, not evidence that the accepted split needs repair.

Under `coord/.merge.lock`, preserved `.bak-Q08-cohomology-20261022` copies
of the Q08 claim and `coord/deliveries.log`, then closed only this stale
claim with `tools/claim.py done Q08`. There is no Q08 delivery branch, open
return, repair note, or live queue row for this item. The six-step Q13
split, its review, and all Lean sources are unchanged. No Lean compilation
is needed for this coordination-only repair.

Validation: stage-1 completion remains true; Q08 no longer holds the item;
the live queue still omits it; the accepted node SHA-256 remains
`0edab0accbbf359736482694119056e087c44080084b4c128b30b3576cf1e7a6`.
A stage-1 take-many attempt must refuse this completed off-queue item.

Launcher follow-up (report only; launcher-owned code is not editable here):
reconcile completed held stage-1 claims that have left the live queue in
`Group.work`, preserving explicit returns and released repair notes. Do
not dispatch them using a remembered stage after `Group.server` reports
`-`. Continue dispatching every listed unclaimed item, as the human
requires; add no failure gates, caps, throttles, waits, or pauses.

Next worker: no new stage-1 split or attachment is due. Keep the accepted
Q13 split. Resume this item only if a live queue row or an explicit repair
reopens it; inspect current Lean source and transitive axioms before any
future attachment claim. The latest live wrapper delegates to another
cohomology theorem, so historical line numbers and the saved sorry text
are not proof certificates.
