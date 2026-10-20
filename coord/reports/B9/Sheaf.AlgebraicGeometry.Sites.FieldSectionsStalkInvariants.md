## What changed

Retired Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants in favor of the
existing unchanged WeilConjectures module and theorem of the same suffix/name.
Updated its DAG realization to the upstream declaration and migrated its three
remaining direct consumers: EtaleFieldSectionsInvariants,
FieldModuleSectionsInvariants, and FieldEquivariantGermsOnePoint.

Two consumers change only a proof import. In onePoint_selected_lift_section,
compose the sheaf with ULift, compare its stalk with the original stalk, and
compose with the existing geometric-point comparison. Use the upstream action
on the lifted stalk, lower germ representatives in the action comparison, and
lower the invariant section before pulling it back. This preserves the exact
smaller-universe statement. Updated the selected-lift DAG proof accordingly.
No source-library file or target was modified; no new declarations were added.
Change record: coord/changes/B9-retire-field-sections-stalk-invariants.md.

Rebased against current source after W2's independent landing of
BaseFieldCohomologicalDimension (ledger 2026-10-20 17:49 UTC,
landing 20261020T174917-L-820235). That module no longer imports the retired item.
Removed its stale adaptation from this packet, preserving W2's newly complete
proof. This repair changes the packet and its ownership/evidence records.
All three retained consumers pass lcompile.py --all (exit 0, cached results).

## Proved and sorry left

The assigned retirement item has zero holes: proved 0 of 0; added 0; split off 0.
Its already proved fieldSections_stalkInvariants is preserved upstream rather
than counted as a newly closed hole. No sorry remains in the withdrawn module.
All three adapted consumers are hole-free. There are no sorry declarations in
the delivered Lean files. W2's independently proved
AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField is not delivered or
counted as progress by B9.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants.
Removed its three remaining direct proof imports and replaced them with the
upstream module. BaseFieldCohomologicalDimension's fourth import was removed by
W2 independently; its stale sandbox adaptation is omitted, not withdrawn.
The withdrawn copy's private action construction, germ-injectivity proof,
and representative-universe bridge are unnecessary duplicates of the upstream
proof. Its dependencies remain needed by that upstream proof and are not claimed
as pruned. No mathematical node or unit step is removed: the invariant-section
node is realized upstream and its parent dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with sorry, but retire-items.tsv
assigns this zero-hole duplicate for retirement. The old kept-twins survey
correctly notes the different coefficient universes; simple import replacement
in the one-point consumer fails with max (u + 1) v = max u v. ULift and the stalk
comparison resolve that interface difference without weakening any consumer.
No current rework row applies to this item.

The return of head e349e7f578 correctly identified a missing forced-adaptation
section and a stale ownership entry: BaseFieldCohomologicalDimension was held by
W2, not unclaimed. This repair records the actual counterfactual failure and
holder, then removes the now-obsolete adaptation after W2's independent landing.
The current consumer has a complete proof and no import of the retired item;
restoring the old sandbox version would wrongly reintroduce a hole.

## Forced adaptations

The returned packet adapted
`Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension`, held by **W2**,
at line 12 only:

```diff
-import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
+import WeilConjectures.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
```

Before the shared checkout refreshed to W2's landing, temporarily restoring the
original consumer while retaining the withdrawal in deleted.txt made deliver3.py
exit 1 before compilation, with this exact original diagnostic:

```text
FAILED: deleted modules are still imported (change these files in the delivery too): lean/Sheaf/AlgebraicGeometry/BaseFieldCohomologicalDimension.lean imports Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
```

This was the actual import/deletion-gate failure, not a Lean elaborator error.
The old compiled module remains in the baseline and withdrawal lands an empty
module, so no missing-import Lean compiler error is claimed. The explicit
withdrawal case of the forced-adaptation check requires migration of such an
import. The replacement imported the retained upstream realization of the same
node; no public signature, attribute, visibility or proof body was changed.
The adapted version compiled with lcompile.py --all (exit 0, 10.4 seconds).

Current resolution: W2's independent landing 20261020T174917-L-820235 already
removes this import and proves the consumer. The stale adaptation is removed
from this delivery entirely. Thus there is no remaining adaptation of a module
held by another group. The change record retains the module name and holder W2
and explains why the returned edit is now unnecessary.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
