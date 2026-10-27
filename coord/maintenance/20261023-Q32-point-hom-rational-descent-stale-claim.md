# Q32 point Hom rational descent: stale stage-1 assignment

Reconciled at 2026-10-23T04:27:06.735284+00:00, under SHEAF_LEAD=L-only and coord/.merge.lock.

Q35 delivered branch head 3701566f8b4. The accepted stage-1 landing is
b45001e76c0 (2026-10-22T11:53:25Z in coord/deliveries.log:53214;
coord/ledger.md:28351), independently reviewed PASS by NT-cc-Q35-3701566f8.
The live item remains split. Q32's replacement claim was created at
2026-10-22T11:53:50Z, 25 seconds after the landing, and subsequently persisted
after the queue stopped listing this item. Its creation was recorded in
30d41242341. The current item has no repair note, Q32 return or delivery branch.

Cause: a stale queue permitted re-claiming an accepted split. Claim policy
intentionally grants listed unclaimed items (human decision 2026-10-22).
In protected dispatch_all.py, Group.server() receives queue_stage=None and
prints '-' for this held claim, retaining the cached stage 1. Group.work()
then treats it as claimed, never-delivered new work without reconciling its
current stage-1 completion. The stage-3 completion check does not cover it.
Q32 workers correctly respected coord/brief-stage1.md's live-wins rule.
All 13 retained Q32 last.txt files end with that substantive BLOCKED answer;
state-batch2.json records 8 tries for the current key. A historical attempt
had recovered HTTP 429 interruptions; they did not cause the stale claim or
these final answers. Provider behavior was not changed or worked around.

After validating authoritative completion, no queue row, no repair order,
no current return and no Q32/Q35 delivery branch, maintenance backed up the
claim and deliveries.log and ran tools/claim.py release Q32 with the reason
below. This reconciles only the obsolete assignment; it does not record a
new mathematical delivery or abandonment.

Release reason: maintenance Q32-1792728729: retire stale stage-1 assignment; Q35 reviewed PASS landed at b45001e76c0 on 2026-10-22T11:53:25Z; no live queue row, released repair, return or delivery; accepted split retained

The commit contains this note, the stale claim deletion, and only the exact
release audit line added to the committed deliveries.log. Other pending
log entries remain in the working tree. Existing-file backups are adjacent
with suffix .maint-Q32-point-hom-1792728729.bak. This new note's empty .md.bak records its prior absence.

Validation: Q32 no longer holds this item; queue_stage is None;
node_finished(item, '1') is True; repair note remains absent. Preserved SHA-256:

- Accepted item: fd60d727990570ea15c41f407b5032d8a55a2b7d9624d8bf14c827652c171a8a
- Q35 report: 104b942b4d7922e9fad3da37c03bc5fd82069afa484d397fe58d88c4a532114f

No node, proof, brief, Lean file, worker sandbox, launcher-owned script,
review service or landing tool was changed. No compile was needed. No
process was killed, and no concurrency cap, throttle, admission limit or
pause was introduced. Pre-reconciliation repository HEAD: 1f3abf609bc0bcee8b4e384ad6a2f307d1a6eaa5.

Launcher-owner follow-up (report only): after a successful authoritative
read, reconcile held stage-1 claims whose completion is established and
which have no current assignment, active delivery, return or released
stage-1 repair. A missing or failed queue read alone cannot establish this.
Preserve listed-item dispatch and genuinely open/reopened work regardless
of failure counts. Reconcile requested stage through the claim/start race.
Protected dispatch_all.py was inspected and not edited.

Next worker: stage 1 is already accepted. Reuse Q35's split and report;
only a new live assignment or released stage-1 repair order can request
further stage-1 work. Future stage-2 formalization is a separate assignment.
Do not manufacture a delivery diff or reopen the accepted proof to satisfy
the stale cached stage. The launcher's historical notes/tries need no reset.
