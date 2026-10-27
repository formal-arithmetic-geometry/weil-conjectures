# Q31 maintenance: lem-per-adic-common-stage-truncations

2026-10-23. Stage-1 dispatch reconciliation only; no mathematics changed.

NI's re-split (delivery 68e487018e3, accepted commit 77a64740622) passed review
at 2026-10-22T11:24:08Z. The stage-1 repair is resolved. Q31 nevertheless
acquired a new claim at 11:25:54Z. That claim remained active under the 72-hour
TTL although the live queue no longer contains the item. Stage 2 already has
an accepted NO statement record. Neither fact proves the Lean theorem.

Eleven Q31 worker runs ended BLOCKED with the accepted split unchanged.
The unchanged-item preflight rejection is correct. There is no outstanding
Q31 return or delivery. The launcher's server() retains its cached stage when
queue_stage returns no stage, and work() redispatches the held item at stage 1.
Launcher code is outside this maintenance authorization; the local REPORT.md
records the required reconciliation of completed held items before relaunch.

Repair: backed up the Q31 claim and deliveries.log, then used tools/claim.py
release Q31 with an explicit completed-stage-1 reconciliation reason. This
removes the obsolete claim without recording an abandonment or changing the
node, repair note, accepted review, Lean module, or any provider settings.
Backups: coord/claims/lem-per-adic-common-stage-truncations.lock.maint-Q31-20261023T0402.bak
and coord/deliveries.log.maint-Q31-20261023T0402.bak.

Validation under coord/.merge.lock: queue_stage is None; node_finished at
stages 1 and 2 is true; the repair is resolved; Q31 no longer holds the item;
a stage-1 take is refused as already completed. SHA-256 checks confirm that
the node, repair note and Lean file are unchanged. No Lean compilation was
needed because no Lean file changed. Existing unrelated work was preserved.

Some historical runs recovered from provider HTTP 429 errors and answered
BLOCKED afterwards; provider remediation is outside scope. No provider or
admission changes were made.

Next worker: there is no stage-1 work on this item unless a new released
stage-1 repair explicitly reopens it. Follow the live queue for remaining
helper nodes and proof work; do not manufacture a diff or re-push NI's split.
