## What changed

Proved both original holes in `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`:
`AlgebraicGeometry.ProEtale.VaryingRing.moduleBetaInv_isIso` and
`AlgebraicGeometry.ProEtale.VaryingRing.moduleOpenToP_isIso`.
The public signatures and definitions are unchanged.  The proof adds three private
categorical imports and private helper lemmas for the levelwise open-unit,
cartesian-base-change, and clopen comparison arguments.  The final module compiles
with `lcompile.py` without errors or warnings.

## Proved and sorry left

Closed the two original sorries, with zero sorries added and zero remaining:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleBetaInv_isIso`
- `AlgebraicGeometry.ProEtale.VaryingRing.moduleOpenToP_isIso`

The proof is by levelwise strict-tower detection and adjunction mate calculations.
The clopen comparison is transported from the normalized derived comparison and its
homology realization.  No definition contains `sorry`, and no new node is needed.

## No longer needed

No imports or dependency nodes were removed.  The proof uses the existing
`VaryingRingOperations`, `ConstantTowerDirectImageNormalization`, and strict-tower
open/proper calculus declarations; all three added imports are proof-only and are
needed for the derived-category and fully-faithful adjunction APIs.

## Where the brief, the DAG or earlier work was wrong

The earlier incomplete version omitted the levelwise helper constructions needed to
apply the strict-tower normalized open and clopen comparisons.  The target statements
and DAG route remain unchanged; no statement is disputed or weakened.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
