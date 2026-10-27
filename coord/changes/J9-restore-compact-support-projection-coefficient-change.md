# Restore the ordinary compact-support coefficient-square dependency

## Cause

The red-build recovery commit 234ab29fac17c49cbba373fd2e61ce7b36a4d6fd removed
landing 20261025T201631-L-2591332 (D6, original commit 10e787e962c) and deleted
Sheaf.Paper.CompactSupportProjectionCoefficientChange along with its other files.
The later N4 landing 20261025T211324-L-3933735 retained an import and application
of compactSupportProjectionCoefficientChange in ordinaryCompletedSquare in
Sheaf.Paper.CompactSupportScalarProjectionIdentification. The dependency DAG node
lem-pur-compact-support-projection-coefficient-change also retained its exact Lean
attachment. No rework/restoration entry existed for the deleted dependency.
Consequently J9 repeatedly failed the source-import gate before compilation.

The recovery log attributes the D6 rollback to ConstantComplexQuotientModel and
ConstantScalarStrictUnit, including the changed unrestricted integral-reduction
interface. This repair restores only the separately needed statement module.
It does not restore the ConcreteIntegralProjectionCone proof or the reverted
IntegralReductionTowerUnrestricted interface.

## Repair

Restore lean/Sheaf/Paper/CompactSupportProjectionCoefficientChange.lean byte for
byte from 234ab29fac1^ (blob daf35b632cc1713240ef01dd8a086446c1b31d8a).
The theorem, its existing named sorry, docstring and public signature are identical
to the previously landed source and the existing DAG attachment. The theorem is
still an open proof obligation; this is source/data repair, not a new proof or a
statement change. No node attachment, route, claim or dispatch counter is changed.

The original source and a record of pre-repair absence are saved as .bak files in
local/maintenance/J9-CompactSupportScalarProjectionIdentification-1792967463/.

## Validation

Single-file compiles through tools/lean_file.sh, in order, with group
MAINT-J9-1792967463 and the normal 60-second acceptance limit:

- CompactSupportProjectionCoefficientChange: exit 0, 3.9 seconds.
- CompactSupportScalarProjectionIdentification: exit 0, 58.4 seconds.

The latter uses the restored dependency compiled in the private group mirror.
The source-import check passes for the consumer and restored dependency. No
compiled object is manually published and no global build is run for this repair;
the ordinary global build must publish the restored module before workers can use
it through their published-build baseline.

## Worker handoff

Retain the J9 sandbox proof of properProjection_existsUnique and its node/report.
Refresh to a base containing this restoration, then rerun the normal delivery
checks. Its previous report records a 55.6-second regular compile but an
87.6-second delivery probe; a remaining time-limit diagnostic must be addressed
by the worker using the normal profiling workflow. This maintenance change does
not validate that unpublished proof or claim it is ready to deliver.

## Pipeline follow-up

Recovery must reconcile newly added modules with the final surviving importers
and DAG attachments. Removing an owning landing must not silently orphan an
independent surviving consumer. Preserve a still-required statement module or
perform a consistent dependent rollback/rework transaction. The landing tools
are outside this maintenance task's editable scope; no tool was modified.
