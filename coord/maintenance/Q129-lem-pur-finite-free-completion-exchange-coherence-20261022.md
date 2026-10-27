# Q129 obsolete stage-1 claim reconciliation

Item: `lem-pur-finite-free-completion-exchange-coherence`. Maintenance at 20261022T103444Z.

Q82's accepted stage-1 split landed at 2026-10-22T06:18:15Z, commit
`a9c4f17b8bf`, reviewer `NT-cc-Q82-0d877656e` (FIX accepted, two new nodes).
The node is split and reviewed pass, retains NG's stage-2 Lean record, and
its stage-1 repair note is resolved. Both claim.node_finished predicates
(stages 1 and 2) are true. The live queue has no row for this item.

Q129 nevertheless acquired its claim at 06:19:34Z, after the landing.
The local dispatcher retained stage 1 when claim.queue_stage returned None:
Group.server leaves the cached stage unchanged and Group.work reschedules
claimed DAG items without reconciling their completed stage. That stale
record caused 40 counted failures at the start of maintenance. The repeated
unchanged-item preflight rejection is correct; the stage-1 live-wins rule
also correctly forbids rewriting an accepted split without a released repair.

Removed only the obsolete Q129 claim under coord/.merge.lock, after checking
the exact claim bytes, current completion, absence from the queue, resolved
repair, and absence of a Q129 delivery branch or open return for the item.
Original claim backup: `/home/ubuntu/weil-maint-bak/Q129-lem-pur-finite-free-completion-exchange-coherence-20261022T103444Z/lem-pur-finite-free-completion-exchange-coherence.lock.bak`.
The accepted node, Lean module, repair note, queue, and other claims are intact.
This dedicated record documents the reconciliation without editing the
shared delivery log or taking ownership of unrelated pending bookkeeping.

Launcher follow-up (protected code; not edited): dispatch_all.py should
reconcile an off-queue held DAG claim against the live completion predicates
before reusing a cached stage or restarting it. Preserve live queued work,
released repairs, current delivery branches and returns; this must not depend
on failure counts or introduce a dispatch pause or limit. The stale-queue
acquisition explains the first claim; the missing held-claim reconciliation
explains its persistence after the queue was refreshed.

Next worker: stage 1 is already accepted. Do not re-split or manufacture a
node change to satisfy the unchanged-item gate. Resume this item only under
a genuinely new live queue assignment or released repair, using the accepted
Q82 node and the existing Lean record as the baseline.

Node SHA256 before reconciliation: 520686a1a60dc3eda9c1b03fb01af868d062646700c354ed341483b8080cefbe.
No mathematics, Lean edits, compiler invocation, provider workaround, launcher
edits, concurrency changes, or process termination were part of this repair.
