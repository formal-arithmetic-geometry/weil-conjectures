## What changed

Retired Sheaf.AlgebraicGeometry.ExternalCupScalarBalance in favor of the existing
WeilConjectures.AlgebraicGeometry.ExternalCupScalarBalance twin. Updated the lean
attachment of lem-sc-external-cup-scalar-balance to that twin and listed the duplicate
file in deleted.txt. The public theorem signature and mathematical proof are retained
unchanged upstream. No consumer source requires editing: the recorded consumer has
already migrated to its upstream twin and imports the retained theorem there.

Change record: coord/changes/M1-retire-external-cup-scalar-balance.md.

Validation: lcompile.py compiled the retained theorem in 13.4 seconds and its upstream
consumer PicardExternalCupScalarComparison in 8.0 seconds. The theorem's axiom probe
reports only propext, Classical.choice and Quot.sound. Source import scans find zero
current imports of the duplicate and zero twin collisions in both retained closures.

## Proved and sorry left

Proved 0 of 0 original sorries; added 0; split off 0. There are no remaining holes
in the assigned module or its retained theorem external_cup_scalar_balance. This is
a duplicate-module retirement and claims pruning, not new mathematical proof progress.
No delivered Lean source adds any declarations or holes.

## No longer needed

Sheaf.AlgebraicGeometry.ExternalCupScalarBalance and its duplicate implementation are
pruned. Its sole public import of
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations remains in
the retained twin; that dependency is still needed. No mathematical dependency node
is pruned: lem-sc-external-cup-scalar-balance, its proof dependencies, and its parent
lem-sc-picard-external-cup-scalar-comparison are all retained. The parent's existing
upstream Lean implementation already uses the retained theorem twice. The unit route
sk-prop-av-cube is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proof work, but the current queue and human-approved
retirement manifest classify this item as retire. It already has a complete proof and
zero holes. N4's recent proof-syntax-only delivery did not retire the duplicate. The
manifest's one-consumer snapshot is stale: that consumer has already migrated to the
upstream twin. The remaining outdated DAG module attachment is corrected here.

The required LeanFinder, Loogle and Mathlib grep searches were run: LeanFinder found
general sheaf-cohomology and injective-resolution APIs; Loogle did not know the local
theorem name; Mathlib grep found no match. Local library search found the exact adopted
twin. The full diff is limited to copyright/spacing, two local instance labels, and
one private proof's equivalent rewrite grouping. There are no new nodes or statements.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
