# Q18 Frobenius cohomology transport: stale claim repaired

Item: `lem-weil-frobenius-cohomology-transport-iso`, stage 1, dispatcher key
`lem-weil-frobenius-cohomology-transport-iso@new` (99 counted failures).
Maintenance time: 2026-10-22T20:07:32Z.

## Cause

Q78's accepted re-split merged as `326e111cc097d7e2407285dbf630c4875352e2eb`
at 2026-10-22T06:59:37Z (reviewer `NT-cc-Q78-808d79bab`). The parent is
`split`, its review passed, and its stage-1 repair note is `resolved`.
All three extracted obligations are now split with passing reviews.
Both the current queue and `coord/queue.tsv` in that merge omit the parent.

Q18 acquired a new claim at 2026-10-22T07:00:54Z, 77 seconds after the merge.
The claim still exists and is unexpired under the configured 72-hour TTL.
The dispatcher reads every held claim in `Group.server()`, but updates its
saved stage only if `claim.queue_stage()` supplies one. Here it returns None,
so the cached stage remains 1. `Group.work()` retries held stage-1 items without
checking `dag_queue.stage1_completed()` or off-queue completion. Its existing
off-queue reconciliation covers stage 3. Each worker therefore correctly
refuses duplicate splitting under `coord/brief-stage1.md:109` and is restarted.
The exact queue snapshot at claim acquisition was not retained; the initial
admission race is inferred. The current stale-claim retry path is confirmed.

The latest run `.1792680127` ended normally with this stale-dispatch answer and
`codex-retry.json` reports `status: answered`, zero recoveries, no last error.
Some older attempts recovered from provider 429 errors. Those provider errors
are outside this repair; they do not explain the identical answers in clean runs.

## Repair

Backed up the Q18 claim and the append-only delivery log, then used
`tools/claim.py release Q18` with an explicit completion reason. This is normal
claim reconciliation, without an abandonment or a new repair order.
The release removes only Q18's obsolete claim and appends its audit entry to
`coord/deliveries.log`. This report and those two record changes are committed
under `coord/.merge.lock`, with `SHEAF_LEAD=L-only` and the requested git identity.
Backup suffix: `.maintenance-Q18-1792699488.bak` (kept on the server).

## Validation and next worker

Before release: the item was held by Q18, off queue, completed for stage 1,
resolved for repair, with no Q18 delivery branch or open return.
After release: it is absent from `claim.held_by("Q18")` and the claim file is
absent. Explicit stage-1 admission is refused. SHA-256 checks confirm that
the parent, repair note, Lean module, and all three extracted nodes retain
their bytes. No Lean file changed, so no compiler or Lake command was needed.

Preserve Q78's accepted split and its three dependencies:
- `lem-weil-point-automorphism-derived-transport-inverse`
- `lem-weil-frobenius-finite-exchange-inverse`
- `lem-weil-frobenius-system-exchange-inverse`

There is no stage-1 work on this parent unless a newly released stage-1 repair
explicitly reopens it. A sorry in its Lean module is a separate proof-stage
obligation, not evidence that this stage-1 split should be repeated.

## Launcher follow-up (protected file; not edited)

In `/home/ubuntu/weil-launcher-all/dispatch_all.py`, reconcile held stage-1
claims before generating another `@new` job: when the current queue omits the
item, the live stage-1 completion predicate is true, no stage-1 repair is
released, and there is no branch or open return to service, release the stale
claim and clear its obsolete stage-specific retry note. Preserve any legitimate
queued work or repair and keep failure counts as history. Recheck a queued
assignment's requested stage against the current queue at admission so a stale
snapshot does not create another obsolete claim. This needs no failure-count
cutoff, throttle, concurrency cap, pause, or provider change. The protected
dispatcher, landing tools, review service, and configuration were not edited.
