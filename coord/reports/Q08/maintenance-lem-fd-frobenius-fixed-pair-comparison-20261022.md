# Maintenance: obsolete fixed-pair comparison assignment

Recorded 20261022T132319Z for Q08 by the maintenance engineer.

The stage-1 re-split was accepted at 2026-10-22T10:58:48Z, in commit
ad7612f313972ef4ee6d15300c87df0fd025d049 (Q35 delivery 11480f1433c).
The node is split and reviewed PASS by NT-cc-Q35-11480f143; its stage-1
repair note is resolved. Its existing stage-2 statement was also accepted.
The three extracted nodes remain genuine stage-1 work with their existing
claims (NV, NR and NU at the time of this repair).

Q08's claim was created at 2026-10-22T10:58:57Z, nine seconds after
acceptance. The current queue no longer lists this item. The dispatcher
continues scheduling held claims and retains the previous stage when
claim.queue_stage returns no row (dispatch_all.py Group.server/Group.stage).
Group.work has no corresponding reconciliation of completed stage-1 held
claims. Every retry therefore received the stage-1 brief, whose live-wins
rule correctly forbids another split. Failure counts are evidence of this
stale record, not a reason to suppress work.

Repair: backed up and released only this obsolete claim using tools/claim.py
release, recording the release in coord/deliveries.log. No node, repair
order, Lean module, accepted report, other claim or queue row was changed.
No process was killed. No compiler or Lake command was run. No concurrency,
admission or retry limit was added.

Backups retained on the server:

- coord/claims/lem-fd-frobenius-fixed-pair-comparison.lock.maint-Q08-fixed-pair-20261022T132319Z.bak
- coord/deliveries.log.maint-Q08-fixed-pair-20261022T132319Z.bak

Before the repair, the current server completion predicate returned true
for stages 1 and 2, queue_stage was None, and a stage-1 take was refused.
After release, this item must not be assigned another stage-1 split unless
an explicit new released stage-1 repair note reopens it. Preserve Q35's
accepted split and continue the three child assignments. The protected
launcher reconciliation gap is documented in the maintenance REPORT.md;
launcher-owned code and dispatcher state were not edited.
