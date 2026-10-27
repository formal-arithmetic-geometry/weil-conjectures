# Maintenance: lem-pod-semilinear-field-operation-lifts / Q12

2026-10-23. The repeated stage-1 failures were caused by an obsolete held claim,
not by missing mathematics. Q23's split c4df5133709 was accepted at
2026-10-22T11:25:12Z (reviewer NT-cc-Q23-c4df51337, PASS); the stage-1 repair
note is resolved. Q12's claim was created at 11:25:54Z, 42 seconds later.
All 16 retained Q12 worker results report this completed assignment; the
dispatcher's failure counter for the current key is 11.

At maintenance, the live item is split and reviewed PASS, both Q23 children
exist, claim.node_finished(item, '1') is True, and queue_stage(item) is None.
No Q12 delivery branch, open return, or active item worker exists. Released
only the superseded Q12 claim with tools/claim.py release under coord/.merge.lock.
Backups of existing changed files are in
~/weil-maint-bak/Q12-semilinear-field-operation-lifts-1792697417/*.bak.

The dispatcher schedules every held claim in Group.work without rechecking
stage-1 completion. Its stage-aware take-many guard cannot repair claims it
already holds. Launcher-owned dispatch_all.py must reconcile held stage-1
assignments against live completion and released repairs before relaunching.
Completed assignments absent from the current queue should be released as
superseded; stage transitions must use current eligibility. Preserve all
genuine open work and repairs; failure counts must never suppress dispatch.
Launcher-owned files were not edited. Current server claim.py already refuses
a fresh off-queue stage-1 claim when this live completion stands.

Separate later DAG defect: c38cb7f5d93 (J3's FieldWeilShriekShiftData landing,
2026-10-22 22:38:34 +08) added the partial stage-3 proof's dependency from
def-zl-field-weil-shriek-shift-data to this parent. The shortest cycle is:

lem-pod-semilinear-field-operation-lifts
 -> lem-pod-weil-frobenius-compact-support-exchange
 -> sk-def-sf-exchanges -> sk-def-sf-operations -> thm-sf-ctf-stability
 -> lem-coef-finite-exceptional -> fix-prop-projection-formula
 -> def-zl-field-weil-shriek-shift-data
 -> lem-pod-semilinear-field-operation-lifts.

The last worker saw a 67-node component; the current live graph has 124 nodes
in this component. This edge was introduced hours after the first repeated
failures. It must be repaired at the FieldWeilShriekShiftData proof dependency
and its corresponding Lean use, using an independent lower-level transport
result. Merely deleting the edge would hide a real proof dependency. This
maintenance does not claim to repair that separate mathematical dependency.

Next worker: stage 1 is complete. Do not alter the accepted parent merely to
pass the unchanged-file gate, re-submit an unchanged sandbox, or claim a Lean
proof is complete. The matching Lean theorem remains sorried. A further
stage-1 change requires a newly released repair with a concrete scope.
No Lean files or tools were changed; no compilation or lake build was run.
