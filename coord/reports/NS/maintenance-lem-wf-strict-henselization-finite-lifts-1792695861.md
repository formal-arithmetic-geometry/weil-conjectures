# NS maintenance: lem-wf-strict-henselization-finite-lifts

The repeated stage-1 dispatch was caused by an obsolete NS claim after Q115's
accepted re-split. This maintenance released that claim through tools/claim.py;
stage 1 is complete. The mathematics and Lean module were unchanged.

Q115's four-node split landed at 80283363c26c282772ce311c096775f7a5459751, with independent reviewer
NT-cc-Q115-07e23a5d1, at 2026-10-22T12:01:43Z
(coord/deliveries.log:53297; coord/ledger.md:28432).
NS acquired the new claim at 12:02:04Z, 21 seconds later. The landing snapshot
still listed the parent as stage 1 in coord/queue.tsv:723. The queue later
dropped it, but the claim survived. Current node predicates report
stage1_completed=True and node_finished(item, '1')=True; the repair note is
resolved and queue_stage=None. NS had no delivery branch or open return for it.

The launcher remembers stage 1 when the claim protocol reports an absent queue
stage, then schedules held, undelivered claims without a stage-1 completion
recheck. The 19 retained worker attempts all answered BLOCKED for the accepted
split; the first five used its separate blocked counter, and the remaining 14
incremented tries. The empty node sandbox is a consequence of avoiding a
duplicate delivery, not lost mathematical work. Historical recovered provider
errors did not cause these completed BLOCKED dispositions; no provider setting
was changed.

Changed records: deleted coord/claims/lem-wf-strict-henselization-finite-lifts.lock using
claim.py release with a completion reason (no abandon prefix), appended the
tool-generated release to coord/deliveries.log, and added this audit. The
transaction and commit run with SHEAF_LEAD=L-only under coord/.merge.lock,
with author Bin Wu <844524296@qq.com>. Only these paths are committed.
Backups: /home/ubuntu/weil-maint-bak/NS-lem-wf-strict-henselization-finite-lifts-1792695861/ (original relative paths plus .bak).

Validation: claim absent after release; no NS-held assignment remains for this
item. The accepted parent, four extracted nodes, resolved repair note, Lean
module, and NS returns retained their SHA-256 hashes. Other NS claim identities
were preserved. No Lean file changed, so no compile was needed.

Launcher-owned follow-up (not edited here): reconcile off-queue held stage-1
claims with live completion and released repair orders before scheduling. Retire
completed claims using the claim protocol, and do not carry a remembered stage
into a new stage's brief. The landing/queue publication path should publish
completed-node state and queue rows consistently. Preserve dispatch of listed,
unclaimed work and failure counting; add no failure-based stop or concurrency
restriction. Details are in the maintenance workspace REPORT.md.

Next worker: do not re-split or redeliver this accepted parent unless a newly
released stage-1 repair order explicitly reopens it. Its four extracted tasks are
lem-wf-henselian-residue-lift-diagram, lem-wf-finite-local-lift-colimit-structure, lem-wf-henselization-ind-etale-comparison, lem-wf-geometric-triples-colimit-comparison.
The existing Sheaf.RingTheory.StrictHenselizationFiniteLifts theorem retains its
own sorry; this bookkeeping correction is not a finished Lean proof attachment.
