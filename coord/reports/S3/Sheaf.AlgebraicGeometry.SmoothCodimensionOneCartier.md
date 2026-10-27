## What changed

Filled the proof of `AlgebraicGeometry.Scheme.Hom.exists_regular_equation_and_isEffectiveCartierCenter_of_smooth` in `Sheaf.AlgebraicGeometry.SmoothCodimensionOneCartier`, preserving its signature and every public import. Updated the node proof and proof dependencies to the implemented route.

On affine charts, apply the existing `Algebra.exists_regularSequence_smooth_surjection` directly. Localize its regular equations to the stalk, identify the quotient using the proved `Scheme.Hom.ker_stalkMap` and the surjective stalk map, and apply Mathlib's regular-sequence dimension formula. Finite-dimensional cancellation gives a singleton list, whose equation is a nonzerodivisor. Off the closed image, the kernel ideal is the unit ideal. These neighbourhoods prove invertibility and the effective Cartier assertion.

Validation: the complete item compiled successfully through `lcompile.py` in 6.0 seconds, with no errors or warnings.

Only proof imports change. Added the smooth-quotient regular-sequence module, the source closed-immersion API, Mathlib ring-hom properties, and flat preservation of regular sequences. No definitions, statements, consumers, or source-library files change.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.Hom.exists_regular_equation_and_isEffectiveCartierCenter_of_smooth` (node `lem-pur-smooth-codimension-one-cartier`). No holes remain in the item; no holes or new declarations are added. No split-off statements.

The proof uses existing library declarations with their existing transitive dependencies. It does not claim their independent completion.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`, and removed its node `lem-pur-smooth-pair-local-coordinates` from this item's proof dependencies: the algebraic regular-equation result already suffices, so the subsequent coordinate lifting and etaleness constructions are unnecessary on this edge. This also bypasses `Sheaf.AlgebraicGeometry.SmoothPairRegularEquations` on this edge by using its algebraic input directly. These modules are not withdrawn; other consumers may still need them.

Removed redundant proof imports `Mathlib.AlgebraicGeometry.AffineScheme` and `Mathlib.RingTheory.Localization.Ideal`; their APIs are available through retained imports. The separate node `lem-weil-pbc-localization-at-prime-of-quotient` is no longer a direct dependency: the already-proved `Scheme.Hom.ker_stalkMap` and quotient-kernel ring equivalence perform the stalk quotient identification. The separate one-equation induction dependency `lem-weil-pbc-dimension-quotient-nonzerodivisor` is replaced by the exact Mathlib leaf `lem-trf-regular-sequence-dimension-formula`. No module is deleted and no upstream declaration is removed or modified.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG planned more coordinate theory and a manual dimension induction than necessary. The direct smooth-quotient regular-sequence theorem and Mathlib dimension formula provide the same argument with fewer dependencies. This node is below the unit level and is not a realized unit statement or step; the unit route is preserved. Empty D is handled by the complement argument, identity immersions cannot satisfy the dimension drop at a point, and arbitrary nonreduced bases remain allowed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
