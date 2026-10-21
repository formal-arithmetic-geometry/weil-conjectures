## What changed

Replaced both original sorries in `Sheaf.Paper.QuotientScalarComparisonDescent` by complete
proofs, preserving every original public declaration and signature.

The model uses `nonempty_derivedChangeOfRingsCochainModel` for ordinary extension and
`exists_compatibleCoefficientTower` for its strict tensor tower. Private balanced section maps
and the sheafification adjunction construct the scalar augmentation. Generator extensionality,
product projections and the fixed Roos coordinates prove naturality and uniqueness.

The level presentations are natural on tensor generators, so K-flat quasi-isomorphism
invariance transports from the existing derived scalar-extension models. Exact products and
the mapping-cone triangle prove Roos invariance. The existing strict homotopy factorization,
resolving-class theorem and pointwise Kan bridge supply the derived universal pair. Full and
essentially surjective precomposition transports it from homotopy categories to complexes.
The Kan universal property gives the comparison; a flat-term K-flat resolution proves its
uniqueness from the required normalization.

For the unit theorem, an explicit sheafified identity-scalar multiplication isomorphism sends
r tensor x to r times x, with inverse x mapped to 1 tensor x. The resulting compatible
level maps have exactly the stated quotient generators, and Roos coordinate extensionality
identifies their augmentation with `roosAugment`.

Private helper arguments adapt existing proved arguments from
`IntegralReductionTowerUnrestricted`, `DerivedChangeOfRingsCochainModel`,
`StrictRoosDerivation`, and `InverseImageTensorPullbackComparison`. No source-library file
was edited. The static interface check requires the scope-command record
`coord/changes/C6-quotient-scalar-private-proof-scopes.md`; it documents the private helper
scopes and byte-for-byte preservation of the public definition. The DAG records the actual route. The source module compiles within the unchanged
60-second limit (28.5 seconds before the final whitespace cleanup).

## Proved and sorry left

Closed 2 original holes:

- `SheafOfModules.quotient_scalar_comparison_descent`.
- `SheafOfModules.quotient_scalar_comparison_unit`.

Added 0 holes; split off 0 statements. No `sorry` remains in any delivered Lean file.
The proof uses existing dependency declarations, including the compatible tower and strict
Roos homotopy theorem, as intended by stage 3. Their unfinished proofs are not new holes.
All new helpers are private and fully proved.

## No longer needed

Removed the private imports `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso` and
`Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso`.

The proof no longer needs node `lem-pur-change-of-rings-kflat-quasi-iso`: the existing
independent-universe cochain derived-change-of-rings model gives the required invariance.
It no longer needs node `lem-pe-roos-coordinates-quasi-iso`: exact products followed by the
mapping-cone triangle prove invariance directly in the actual strict Roos model. Removed
that obsolete node from this node's `tool_uses`. These are dependency removals for this item;
no other module or declaration is withdrawn.

Added private imports for the compatible tower, cochain scalar-extension model, upstream
`DerivedCategory.TowerLimit` (its proved limit-map quasi-isomorphism lemma), Mathlib exact
limits and initial functors, and the independent tensor-colimits comparison. Original public
imports are unchanged. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned change-of-rings invariance lemma uses more restrictive universes than the item;
the existing independent-universe cochain model supplies the correct interface. The planned
coordinate-reordering lemma is unnecessary for the actual mapping cone. The unit proof does
not need the compatibility hypothesis `hc` beyond the input tower interface: the model's
transition formula and the augmentation coordinates already imply its conclusion.

No false statement or definition repair was needed. No new nodes were introduced.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
