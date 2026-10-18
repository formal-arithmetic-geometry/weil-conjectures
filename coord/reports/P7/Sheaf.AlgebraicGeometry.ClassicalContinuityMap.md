## What changed

Filled the proofs of `continuityMap_ι`, `continuityMap_natural`, `isClassical_iso_iff`,
`isClassicalModule_iff`, `isClassicalComplex_Q_iff`, and `isClassicalComplex_iso_iff` in
`lean/Sheaf/AlgebraicGeometry/ClassicalContinuityMap.lean`. Removed four unused private
imports (`ModuleCat.AB`, `CommAlgCat.Basic`, `RingHomProperties`, and
`GammaSpecAdjunction`).

## Proved and sorry left

Six of the seven original sorries are proved: `continuityMap_ι`, `continuityMap_natural`,
`isClassical_iso_iff`, `isClassicalModule_iff`, `isClassicalComplex_Q_iff`, and
`isClassicalComplex_iso_iff`. The original sorry in `affinePresentation_iff` remains; no
new sorry was added.

## No longer needed

The proof does not use the four removed private imports listed above. No DAG dependency
node was added or removed; the remaining affine presentation theorem still follows the
recorded final proof steps as an open statement.

## Where the brief, the DAG or earlier work was wrong

The affine presentation equivalence has an index category in `Type (u + 1)`, while
`proAffineEtale` is defined using `MorphismProperty.pro.{u}`. The available
`pro_of_univLE` lemma only transports from a smaller universe to a larger one, so it
cannot reduce the presentation obtained directly from the `pro` witness to the required
`Type u` index. Establishing that universe-shrinking theorem requires additional
finite-presentation/descent infrastructure beyond the available declarations.

## New nodes

None.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
