## What changed

Completed the zero-hole retirement repair listed in coord/retire-items.tsv.
Withdrew Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore and
repointed lem-sc-separated-affine-function-field-surjective-core to the identical
proved declaration in its WeilConjectures twin. No upstream source is changed.
The extra unused surjective_of_isClosedImmersion_specMap has the proved upstream
equivalent surjective_of_isClosedImmersion_SpecMap in
WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel.

Change record: coord/changes/retire-separated-affine-function-field-surjective-core.md.

## Proved and sorry left

The item initially had zero sorries. Holes closed: none (0 of 0). Holes added:
none. Sorries left in delivered modules: none. This is a retirement repair,
not a new proof or decomposition. Both original theorems were already proved.

The original module compiled before withdrawal. A scratch check imports the
upstream core, its upstream consumer, and ProjectiveSpace.CoordinateModel;
it applies the upstream surjectivity lemma with the exact old proposition and
prints axioms of the upstream closed-immersion theorem, surjectivity lemma, and
separated-affine function-field surjectivity theorem. This check compiled in
1.4 seconds; all three declarations use only propext, Classical.choice, and
Quot.sound. The original module compiled in 2.0 seconds without warnings.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore.
All imports of that module disappear with it: Mathlib.AlgebraicGeometry.FunctionField,
Mathlib.AlgebraicGeometry.Morphisms.Separated,
Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, and the proof import
WeilConjectures.AlgebraicGeometry.AffineLocalFunctionFieldDiagonalPullback.
These supporting modules and nodes remain needed by the upstream proof; none
is claimed globally unnecessary. The existing node is retained and points to
the upstream twin. No other node or module is pruned.

The duplicate AlgebraicGeometry.Scheme.isClosedImmersion_specMap_tensor_functionField
and unused AlgebraicGeometry.surjective_of_isClosedImmersion_specMap are removed
from the Sheaf copy. All live mathematical obligations remain in upstream modules.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a sorry-bearing module, but the actual queue
item is a retirement repair with zero holes. The retirement table's sole listed
consumer, Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective, has
already been retired in the current shared tree. No adaptation is needed:
rg over both roots finds no import or external reference to the copy, and both
downstream.py --uses queries find zero downstream modules. Its upstream consumer
already imports the upstream core and applies the differently capitalized
surjective_of_isClosedImmersion_SpecMap from ProjectiveSpace.CoordinateModel.

The core node still pointed to the redundant Sheaf copy; this delivery corrects
only its Lean attachment. The unit route, node statement, and proof plan stay intact.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
