## What changed

Restored Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange from the
quarantine path in its current rework row. The public theorem
AlgebraicGeometry.nonempty_derivedBaseChange_iso_of_isFlatOver keeps its original
signature, including the four HasDerivedCategory hypotheses and arbitrary
universe w. It now has a complete proof.

The existing proved exists_isIso_canonicalModuleBaseChange_of_isFlatOver follows
the same affine Cech argument. Apply it in the Grothendieck model in universe u,
then compare both endpoints with DerivedCategory X.Modules and transport the
result back to the four given localizations. Six proved private helpers supply
the model comparisons. In particular, both direct images are computed using
the same K-injective resolution. No global instance in universe w is assumed.

Replaced the retired public Sheaf derived-pullback import with the adopted
WeilConjectures module, removed unused BaseChangeConventions, and narrowed the
DirectImage public import to DirectImage.Basic. Updated the existing node's
proof, proof_deps and proof_origin; retained its Lean attachment and all
mathematical statements. No source-library file is edited.

The restored module compiles in 5.5--5.8 seconds. Its public theorem's axiom
check reports exactly propext, Classical.choice and Quot.sound. The original
quarantined ArrowIsoTensorPullbackCounit consumer also compiles unchanged
against this restored module in 5.1 seconds. Its own existing sorry is not
changed or delivered. The signature was compared textually with the archive;
all lines are at most 100 characters.

The downstream.py --allow-missing --uses query reports zero live importers
and zero live declaration users; archived and DAG consumers are retained.

Change record: coord/changes/Y3-relatively-flat-base-change-restoration.md.

## Proved and sorry left

Closed one archived hole:
AlgebraicGeometry.nonempty_derivedBaseChange_iso_of_isFlatOver
(lem-pc-rf-base-change-flat-module).

Original item: 1 sorry. Delivered item: 0 sorries. Added: 0. Split off: 0.
The six private helpers are all proved. This is a proof, not a decomposition.
The full public theorem is free of sorryAx, as its axiom check confirms.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.BaseChangeMapCech
- Sheaf.AlgebraicGeometry.CechResolution
- WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
- WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

Removed public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
replaced public Sheaf.AlgebraicGeometry.DerivedPullback with its adopted source;
narrowed public WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage to .Basic.

The item's direct proof_deps no longer include lem-pc-base-change-map-cech,
lem-pc-cech-resolution, lem-pc-flat-complex-derived-pullback or
lem-weil-pbc-module-pullback-affine-sections: the existing canonical theorem
packages that argument. This is removal of direct obligations only. The
canonical source proof still reaches flatComplexDerivedPullback and the
source affine-section comparison transitively, so neither is globally pruned.
No source declaration or module is deleted, and no claim of globally pruning
the legacy Cech modules is made while other consumers may need them.
No new module is introduced.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it is quarantined, not because it is
unused. Restored its preserved statement and kept its node and unfinished
DAG parents. The recorded duplicate-derivedPullback import failure is repaired
by following the already-landed B2 source-construction migration.

The literal baseChangeMap_cech signature does not assert its docstring's Cech
identifications or comparison equation (its source already warns of this).
It cannot provide the originally planned final canonical-map argument.
The existing proved canonical theorem supplies that argument, including its
finite affine Cech model, flat-complex calculation, section comparison and
local-to-global step. Its node is
lem-pc-relatively-flat-canonical-module-base-change, in another Picard unit;
it is used as an existing proved tool for precisely the same lower-level
argument, without bypassing any unit statement or prescribed realized step.
The sk-thm-picard-semicon realized statement/step lists are empty.

The canonical theorem has a stronger localization-instance interface than this
item. The private comparisons are necessary to preserve the original four
instance hypotheses and arbitrary universe, instead of silently strengthening
the statement. Empty schemes, zero modules and arbitrary g remain included;
none of the model comparisons requires a point or a nonzero ring.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
