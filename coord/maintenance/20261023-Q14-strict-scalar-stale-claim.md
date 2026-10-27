# Q14 strict-scalar-composition stale stage-1 claim reconciliation

Reconciled at 2026-10-22T19:39:08.291496+00:00.

Q46's accepted stage-1 split is commit 58506093e93, reviewed PASS by
NT-cc-Q46-0590f63bf. coord/deliveries.log records completion at
2026-10-22T09:23:58Z; the commit is dated 09:23:59Z. Q14 acquired its claim
at 09:24:05Z, six seconds after the commit, from the old stage-1 queue.
The first worker already found the accepted live split. All repeated
unchanged-item rejections are the correct outcome of an obsolete assignment.

The claim remained active: its t value was 1792661045.9735827 and the
configured TTL was 259200 seconds (72 hours). At reconciliation the
item had no row in any coord/queue*.tsv; claim.queue_stage returned None,
claim.node_finished(item, "1") was true, node_finished(item, "2") false,
and there was no repair note, Q14 return, or Q14 delivery branch.
The live node and retained Q14 sandbox had the same SHA-256:
39768a2393632a04c260b39eb15f07990000c3193fd02420892549a5c310afd6.

Cause: a post-landing stale queue/claim race, followed by the protected
launcher's held-claim fallback. tools/claim.py take honors the human's
2026-10-22 instruction to grant listed, unclaimed work. When the queue row
then disappeared, dispatch_all.py Group.server did not replace the cached
stage because queue_stage supplied no stage; Group.stage kept stage 1,
and Group.work repeatedly dispatched the held claim without reconciling
live stage-1 completion. This was not a missing mathematics repair order
or a defective unchanged-item gate.

Under SHEAF_LEAD=L-only flock coord/.merge.lock, maintenance rechecked the
exact owner/timestamp, stage predicates, review, queue absence and lack of
an outstanding repair/delivery, then ran tools/claim.py release Q14 with
an explicit reconciliation reason. The claim was deleted and its release
was appended to coord/deliveries.log. This closes a completed assignment;
failure counts are retained and future open work follows the normal queue.

Changed paths:
- coord/claims/lem-pur-compact-support-strict-scalar-composition.lock: obsolete claim removed.
- coord/deliveries.log: normal claim.py release record.
- coord/maintenance/20261023-Q14-strict-scalar-stale-claim.md: this maintenance record.

Backups:
- coord/claims/lem-pur-compact-support-strict-scalar-composition.lock.maint-Q14-1792697655.bak
- coord/deliveries.log.maint-Q14-1792697655.bak
- coord/maintenance/20261023-Q14-strict-scalar-stale-claim.md.bak (new record snapshot).

No DAG node, repair note, brief, Lean source, worker sandbox, launcher
implementation, review service or landing tool was changed. No compiler
or lake build was needed. No process was killed, and no cap, throttle,
admission limit or pause was added.

Protected launcher follow-up (recorded here; implementation not edited):
reconcile held stage-1 assignments after a successful live read establishes
no current queue row, no outstanding stage-1 repair/delivery, and true live
stage-1 completion. Carry requested stage through the queue/claim/start
race, and reconcile a later stage from authoritative live state. Preserve
the human's listed-item dispatch rule, released repair orders, explicit
returns, and all work that is still open; an absent/failed read alone is
not evidence of completion. Never use failure counts as a dispatch filter.

Next worker: stage 1 is already accepted at 58506093e93. Preserve that
split and its existing dependency tasks. Do not manufacture a node diff
to bypass the unchanged-item gate or create an unsupported repair note.
A future stage-2 assignment must follow the live queue and its brief;
this release does not claim Lean completion. The Q14 sandbox is historical
diagnostic material, not an undelivered replacement for the accepted split.
