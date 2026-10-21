# NK maintenance: completed fixed-pair truncation item

Recorded 2026-10-21T17:42:16Z for `lem-pod-fixed-pair-truncation-cohomology@new`, stage 2.

The failure was a stale server claim, sustained by the launcher's held-claim
reconciliation. Q19 completed stage 2 at 2026-10-21T16:34:48Z in merged commit
`cb24f94869b`; `coord/ledger.md:23054` records reviewer PASS. The node records
`reviewed_lean.result = pass` (reviewer `NT-stage2-cc-e43adf107`).
`coord/queue-states.tsv` marks stage 2 done at 2026-10-21T16:39:27Z.
NK's claim was created at 2026-10-21T16:34:53Z, five seconds after completion.
At maintenance time it remained held although the queue no longer listed the
item, there was no delivery branch, open NK return, or repair note, and
`claim.node_finished(item, "2")` was true.

Released only that obsolete claim with `tools/claim.py release NK` and a
completion reason. The tool appended the release to `coord/deliveries.log`.
Backups of both modified records:

- `coord/claims/lem-pod-fixed-pair-truncation-cohomology.lock.maint-NK-1792604148.bak`
- `coord/deliveries.log.maint-NK-1792604148.bak`

Validated that the claim is absent, NK no longer holds the item, and the
stage-aware take operation refuses it as already completed. The source
`lean/Sheaf/Paper/FixedPairTruncationCohomology.lean` is unchanged (SHA-256 `68d0b0fab019a6b930ed8312d0c2997eedf04b9aafa008419c38337033488b20`).
No Lean compilation was needed for this claim-record correction.

Launcher follow-up (protected code, not modified): `dispatch_all.py`'s
`Group.work()` uses held claims as new work and does not reconcile completed
stage-2 nodes, unlike its stage-3 completion check. Reconcile server-authoritative
stage-2 completion before adding held claims or pending requests to the worker
list, preserving explicit repair handoffs and returns. This is completion
bookkeeping, independent of failure counts; add no pause, throttle, or limit.
The local maintenance `REPORT.md` contains the full handoff.

The next worker should treat stage 2 as completed by Q19. Do not re-record its
Lean ownership or push a duplicate packet (delivery-errors.md A7). New work
requires an identified defect and an explicit repair brief.
