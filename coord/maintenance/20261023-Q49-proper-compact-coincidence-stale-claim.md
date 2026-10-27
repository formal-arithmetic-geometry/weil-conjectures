# Q49 obsolete stage-1 claim: proper compact coincidence

Maintenance on 2026-10-23 for `prop-weil-proper-compact-coincidence@new`.

Q111's three-node re-split landed as
`f220580fbac7b672500c46a4a3bd6bd27a016ac4` from delivery `ddbb3e61a1b`,
reviewed by `NT-cc-Q111-ddbb3e61a`. `coord/deliveries.log` records completion
at 2026-10-22T09:17:58Z; the landing commit is dated 09:17:59Z.
Q49 acquired its claim at 09:18:04Z, six seconds after the completion event.
Its first worker already reported the accepted live split and resolved repair.
The maintenance trigger counted 48 failures. There are 53 historical attempt
directories, so directory count must not be substituted for dispatcher tries.

The authoritative live checks found status split, reviewed PASS by Q111,
resolved stage-1 repair, stage1_completed true, node_finished true for stages
1 and 2, queue_stage None, no Q49 return, and no Q49 delivery branch.
Q49's claim was still active because the configured TTL is 72 hours.
The sandbox item and live node have the identical SHA-256 below.

Cause: a queue/claim race after landing left an obsolete stage-1 assignment.
The historical queue snapshot is not retained here; the post-landing claim
timing establishes the stale assignment. The current claim implementation
allows listed unclaimed items under the human's listed-item rule. Once the
queue drops an item, protected dispatch_all.py Group.server() receives no
queue stage and retains the saved stage; Group.work() repeatedly dispatches
the held claim without reconciling stage-1 completion. Preflight's unchanged
item rejection and the brief's live-wins instruction are both correct. A
cosmetic node edit or another split would corrupt the accepted workflow.

Under SHEAF_LEAD=L-only and coord/.merge.lock, maintenance rechecked the
exact claim owner and timestamp, completion and repair state, absence from
the queue, and absence of an open return or delivery. It backed up the claim
and deliveries log, then used tools/claim.py release Q49 with an explicit
completed-work reconciliation reason. This removes obsolete work; it is not
an abandonment, throttle, failure-count gate, or pause of eligible work.

Validation: the claim is absent, Q49 no longer holds the item, the queue
still has no item row, and a real stage-aware claim.take(..., stage='1')
refuses it as already completed. The accepted node, resolved repair record,
and Lean module retain these SHA-256 values:

- dag/nodes/sec-zeta-weil/prop-weil-proper-compact-coincidence.json:
  715d572863eaa52f7770bd3975204b1727229eea2c2db74d412e3d3f9fd64dfc
- coord/repair-notes/prop-weil-proper-compact-coincidence.json:
  bcf022a18ea1c1a51449bba11fdb8fee4b2ae363ad9043bbbb16963c297d455d
- lean/Sheaf/Paper/ProperCompactCoincidence.lean:
  282843e36ffe783da3d20ad8529611496a151daf585f1808152374cbac8205dd

Changed server paths:

- coord/claims/prop-weil-proper-compact-coincidence.lock: obsolete claim removed.
- coord/deliveries.log: normal release event appended.
- coord/maintenance/20261023-Q49-proper-compact-coincidence-stale-claim.md:
  this audit record.

Server backups, not staged:

- coord/claims/prop-weil-proper-compact-coincidence.lock.maint-Q49-1792728897.bak
- coord/deliveries.log.maint-Q49-1792728897.bak
- coord/maintenance/20261023-Q49-proper-compact-coincidence-stale-claim.md.bak
  (snapshot of this newly created record).

The commit contains only these three paths and only this maintenance event
from the shared deliveries log; concurrent uncommitted events are retained
in the working file. No launcher implementation, dispatcher state, failure
count, worker sandbox, DAG node, repair note, or Lean source was edited.
No Lean compilation was necessary for this coordination repair. No process
was killed, and no concurrency or admission setting was changed.

Protected launcher follow-up, report only: reconcile held stage-1 claims
against an authoritative current queue and live stage completion, while
preserving open returns, outstanding deliveries and released stage-1 repairs.
Release an obsolete completed assignment instead of indefinitely retaining
its saved stage when queue_stage is None. A failed read alone is not evidence
of completion. Preserve the human's dispatch rule for genuinely listed work,
and never use the number of failures as a dispatch condition.

Next worker: stage 1 is already accepted. Preserve Q111's split and its three
extracted tasks: lem-weil-proper-finite-normalization,
lem-weil-proper-integral-tower-comparison, and
lem-weil-proper-coefficient-descent. Follow their current individual records
and queue stages. The parent has a Lean interface at
Sheaf.Paper.ProperCompactCoincidence; a stage-2 record is not a proof
certificate. Only a new live assignment or explicitly released repair
authorizes more work on the parent. Do not rerun the old Q49 unchanged
delivery, invent ATTACH, or report a new DELIVERED result. Historical attempt
logs and the sandbox are retained by this maintenance action.
