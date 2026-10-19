# pur713-def-kflat-module: duplicate delivery retired

The stage-2 statement already landed from Q47: delivery 2e7c344fecb9d6b301f59a41d8a10cfe4d041c07, reviewed
PASS by NT-stage2-cc-2e7c344fe, landing commit 7b7d3c124e (batch
9b58f88bd470494db69e835681952bb2, deliveries.log at 2026-10-18T03:52:47Z).
NS was claimed at 03:53:08Z and submitted bad670a915b83109bfd4ad4cf56bdec5bb83b116; its node/module
diff consists only of Q47 -> NS attribution changes. The immutable return
ed26e4422e169acc36f3813290d6c6ca32dbe0d2 explicitly instructed DROP.

The branch was already archived at
refs/stage2-returned/NS/pur713-def-kflat-module/bad670a915b83109bfd4ad4cf56bdec5bb83b116, but NS's
claim and open return remained. The dispatcher parses every headed return as
repair work while the claim is held. Its repair brief requires compilation and
delivery, while worker-brief2 permits ABANDON only for a faulty unit statement.
Workers restored Q47 attribution correctly, then repeatedly ran a delivery
preflight which correctly rejects unchanged landed files and lean.by=Q47 in an
NS packet. This was stale coordination state, not a mathematical/compiler defect.

Maintenance removed only the obsolete return entry and closed NS's stale claim
with claim.py done, explicitly recording Q47's completion. The original return
is preserved below and in its original commit. No node, Lean source, attribution,
review, queue, dispatcher, review service, landing tool or provider setting was
changed. Failure counters remain historical evidence.

Validation: tools/lean_file.sh lean/Sheaf/Algebra/Homology/KFlatModuleObject.lean, bounded by timeout 60s,
completed cleanly in 2.6 s (nice 19, two threads). The module SHA-256 is
6887f413425c02deea420ea2639f7fbee12d5c1c771638362ae122016cb62bb6.
The saved sandbox node/module matched the shared checkout byte for byte.
Before closing, stage2_finished was true and the current queue did not list the item.

Next worker: stage 2 is complete. Preserve Q47's lean and reviewed_lean records;
do not manufacture an NS delivery or copy another group's report. A fresh
repair requires a substantive defect and a new explicit maintenance request.

Launcher follow-up is documented in the maintenance REPORT.md: terminal DROP
returns must be reconciled with claim ownership rather than sent as repair work;
fresh stage-2 claims also need a completion check against stale queue rows.
These launcher/landing changes are outside this maintenance edit authorization.

Backups (server, existing files before this transaction):
- coord/returns/NS.md.pur713-maint-20261018T042229Z.bak
- coord/deliveries.log.pur713-maint-20261018T042229Z.bak
- coord/ledger.md.pur713-maint-20261018T042229Z.bak
- /home/ubuntu/weil-newtargets/coord/claims/pur713-def-kflat-module.lock.pur713-maint-20261018T042229Z.bak

Original retired return:

## pur713-def-kflat-module (2026-10-18 04:04 UTC, branch head bad670a915)

L: independent stage-2 immutable head bad670a915b8: Drop the delivery; do not re-deliver. pur713-def-kflat-module already landed from Q47 (2e7c344fecb9, reviewed pass by NT-stage2-cc-2e7c344fe). This delivery differs from the live files only in the group name. Node: lean.by changes Q47->NS while Q47's reviewed_lean is kept, which misattributes the landed statement (H2). Module: only the Authors line changes; the same three declarations already exist on newtargets-dag (H4/H9). Report: Q47's report word for word with Q47->NS, including Q47's compile timings and searches, so the second reading is not a reading (H11). The mathematics is correct and the statement is the landed one: arbitrary CommMon R, Mod.monoidalCategory, HomologicalComplex.tensorObj with sign (-1)^p, one-sided acyclic test, P->M quasi-iso resolution, functorial Q with q : Q => id, sorry only in the theorem. nt_compile of the live module, which differs only in a comment: clean in 2.3 s.
