# Q20 chartwise etale permanence: obsolete stage-1 claim

Maintenance of lem-trf-space-chartwise-etale-permanence@new, 2026-10-23.

Cause: Q118's independently reviewed three-node re-split landed in
`d0bd8c7056074ba44ee66ed4ada958d5b348ef1f` at 2026-10-22T06:50:19Z
(coord/deliveries.log; coord/ledger.md). Q20's claim was created at
06:51:03Z, after that completion. The repair note is resolved, the node is
split with Q118/pass review, and the existing Q03 Lean statement has a
passing review. Both claim.node_finished(item, '1') and (..., '2') are true.
The item is absent from queue.tsv, queue-batches.tsv and queue-batches-all.tsv.
It has no Q20 delivery branch or open return.

The dispatcher still enumerated the claim as held. Its server() updates a
cached stage only when queue_stage supplies one; this item supplies None.
Its cached stage therefore remained 1. work() rechecks completion for held
stage-3 modules but not held stage-1 items, and reschedules each BLOCKED
answer as new work. The sandbox node is byte-identical to the live node
(SHA256 42db9fee2c54e3b69b3c6e2972d019091b2e021dda3570a4ac25b1b1c87f0699).
The unchanged-item preflight is correct; the assigned work was already done.
Failure counts are not the cause and must never gate dispatch.

Repair: backed up and released only Q20's obsolete claim using
`tools/claim.py release`, with the completion evidence in deliveries.log.
The release, this report and ledger entry are committed under coord/.merge.lock.
Backups of the removed claim, deliveries.log and ledger.md have suffix
`.maint-Q20-chartwise-1792698806.bak`; a snapshot of this report has it too.
The maintenance workspace also holds retained-worker-sandbox.tar.gz.bak,
because normal dispatcher cleanup may remove a sandbox after release.

Validation: under the merge lock, verified stage-1 and stage-2 completion,
resolved repair note, absence from all three queues, no item-specific Q20
return or delivery branch; after release verified the claim is absent,
other Q20 claims are unchanged, and the node, repair note and returns file
are byte-identical. No Lean file changed, so no compile is needed.

Launcher follow-up (not applied; dispatch_all.py is launcher-owned): reconcile
held claims with live stage completion before scheduling retries. For an
item absent from the live queue, with completed stage and no released repair,
open item return or delivery awaiting review, release the obsolete claim
through the server claim tool and clear obsolete stage/note data. Preserve
listed work and real repair handoffs. A missing queue stage must not make a
historical stage assignment into new work. Do not use failure counts, pauses,
backoff or admission limits. Current claim.take already rejects this item
while it is unlisted and complete; changing the human's listed-task policy
is neither necessary nor intended.

Next worker: there is no remaining stage-1 job on this node. Preserve Q118's
accepted split and the resolved repair. Only a new explicit repair order
reopens stage 1. The existing theorem still has a sorry; its eventual proof
is a separate stage-3 task under normal target routing.
