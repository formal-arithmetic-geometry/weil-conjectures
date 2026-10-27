# NH obsolete stage-1 claim reconciliation

Item: `lem-trf-hilbert-samuel-local-presentations`.

Q158's independently reviewed split landed at `e3fdd555cbd` at
2026-10-22T07:55:52Z (reviewer `NT-cc-Q158-a978f46b2`). The released
stage-1 re-split note was resolved by that landing. NH's claim was created
at 07:56:01Z, nine seconds later, while the queue was being refreshed.
The item is now absent from the live queue and both stage-1 and stage-2
completion checks return true. NH has no delivery branch or open return.

The launcher retained stage 1 when claim.queue_stage returned None and
continued dispatching the held claim as new work. Each worker correctly
kept the accepted split; the unchanged-item preflight correctly refused a
second delivery. This was a stale coordination claim, not a missing proof
or a failed review.

Maintenance backed up the NH claim and deliveries.log, released only the
obsolete NH claim through tools/claim.py release, and recorded this note.
The accepted node, Lean records, sources and resolved repair note were
verified unchanged. The normal release is not an abandonment and does not
change failure counters or restrict dispatch of open work.

Validation: live queue absent; stage-1/stage-2 finished; repair resolved;
no NH branch/return; claim.take(stage=1) refused before mutation. After
release NH no longer holds the item. No Lean file changed or was compiled.

The launcher owner should reconcile already-held stage-1/2 claims against
the live stage-completion state before restarting them, preserving genuine
released repairs and open returned deliveries. An absent queue row must
not indefinitely reuse a saved stage for completed work. dispatch_all.py
is launcher-owned and was not edited by this maintenance task.

Next worker: no stage-1 delivery is owed here. Preserve Q158's accepted
split. Further work belongs to its open prerequisites or a newly released,
explicit repair; sorry-bearing Lean statements do not reopen stage 1.
