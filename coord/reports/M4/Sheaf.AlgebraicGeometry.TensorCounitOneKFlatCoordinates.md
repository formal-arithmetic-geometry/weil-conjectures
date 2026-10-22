## What changed

Restored lean/Sheaf/AlgebraicGeometry/TensorCounitOneKFlatCoordinates.lean from its
quarantined state as a compatibility import of
WeilConjectures.AlgebraicGeometry.TensorCounitOneKFlatCoordinates. Preserved the
original public CanonicalPullbackTensorComparison import and its legacy K-flat
vocabulary. The adopted source already proves the full coordinate theorem.

Redirected lem-pc-tensor-counit-one-kflat-coordinates's Lean attachment to that source
module, recording its actual signature. Kept the mathematical statement, dependency
lists, proof plan and unit route unchanged. The archive remains in quarantine.

Change record: coord/changes/M4-tensor-counit-one-kflat-source-compatibility.md.

## Proved and sorry left

This is a zero-hole repair. The archive contained zero sorries; the restored module
contains zero sorries. Holes closed: none (0). Holes added: none (0). Split off: none (0).
AlgebraicGeometry.tensorCounit_oneKFlat_coordinates is supplied by its existing adopted
proof; no duplicate declaration is introduced.

Validation: the restored module compiles. A separate sandbox consumer reproduces the
archived theorem result with the legacy IsAcyclicTensorKFlat hypothesis and applies the
adopted theorem. Local letI bindings cache the available small colimits and total-complex existence
proofs; they introduce no hypothesis. It also checks the polymorphic equality of the old
and new K-flat predicates by rfl. The source theorem axiom check lists only propext, Classical.choice and Quot.sound.
The full consumer compiled in 10.2 seconds, with the same three axioms.
The compatibility module compiled in 1.9 seconds; import_direction.py permits the import.

## No longer needed

No mathematical dependency, node or module is pruned. The existing parent node
lem-pc-rf-base-change-complex still needs this coordinate theorem. All source-library
declarations and imports are retained unchanged.

The restored compatibility module does not repeat the archive's private proof imports:
Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct,
Sheaf.Algebra.Homology.KFlatPullback,
WeilConjectures.AlgebraicGeometry.TensorCounitCoordinateEquation,
Sheaf.Algebra.Homology.KFlat,
Sheaf.Algebra.Homology.KFlatResolution,
Sheaf.AlgebraicGeometry.DerivedPullback,
WeilConjectures.AlgebraicGeometry.DerivedTensorStructure,
WeilConjectures.AlgebraicGeometry.ModulePullbackTensor, and
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition.
These dependencies are supplied by the adopted implementation and the retained public
canonical comparison import. This removes duplicate implementation, not needed theory.

## Where the brief, the DAG or earlier work was wrong

The current assignment is a quarantined zero-hole repair rather than an unproved lemma.
Restoring the archived file unchanged fails at line 159 during HasColimit synthesis.
The exact coordinate theorem already exists in the adopted source library. The earlier
retirement census labeled this pair DIFFERENT because IsAcyclicTensorKFlat was renamed
to IsKFlatTensor upstream; the full predicate definitions agree by reduction. The source
also supplies explicit category arguments to curriedTensor. A mechanical comparison of
the full signatures after just those two substitutions and whitespace normalization
finds no other difference. The archived theorem type is preserved by the compatibility
restoration.

The missing item's tools/downstream.py query reports unknown module(s); an exact search
of current and quarantined modules finds the archived RelativelyFlatDerivedBaseChangeComplex
consumer. Its theorem application is covered by the legacy-predicate consumer check.
The old M4 return contains only the general upstream-rebase notice, no numbered repairs.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
