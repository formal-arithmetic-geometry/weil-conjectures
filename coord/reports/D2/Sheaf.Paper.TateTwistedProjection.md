## What changed

Filled the two canonical-map uniqueness proofs in
`Sheaf.Paper.TateTwistedProjection`, preserving all declaration signatures,
definition bodies, imports and normalization predicates. Both proofs unfold
the fixed native tensor bundle to identify the shared tensor with the
published tensor. The tensor-shift proof also reduces the recorded twist
functor and explicitly names `CondensedRing.derivedTensor`. Its witness is
the specified commutation isomorphism. The projection-family witness is the published projection mate
at each argument; function extensionality proves uniqueness.

## Proved and sorry left

Closed two existing holes:

- `AlgebraicGeometry.ProEtale.RationalP1.tensorShift_existsUnique`.
- `AlgebraicGeometry.ProEtale.RationalP1.projectionMate_existsUnique`.

Both belong to `def-sfb-tate-twisted-projection-comparison`. No holes remain
in the item, and no holes or modules were added. The canonical constructions
continue to use their existing uniquely determining predicates.

## No longer needed

None. No imports, nodes or modules were removed. All existing statement
and construction dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The rework table retains an old quarantine entry, but the live item source
is present and agrees with the quarantine copy. This delivery starts from
the live source and preserves the attachment and all dependencies.

The two holes are normalization and extensionality obligations; neither
requires proving the projection formula or a new tensor-shift theorem.
Library search found `existsUnique_eq` in Mathlib and the analogous proved
`singleUnit_existsUnique` in `Sheaf.Paper.ProjectiveDiagonalPullback`.
LeanFinder, Loogle, Mathlib grep and project grep were consulted before
writing the proofs. The existing docstring arguments are followed exactly;
the unit route is unchanged.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
