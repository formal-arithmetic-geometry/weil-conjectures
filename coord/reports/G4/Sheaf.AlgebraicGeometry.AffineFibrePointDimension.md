## What changed

Filled `AlgebraicGeometry.affine_fibre_point_dimension` in
`Sheaf.AlgebraicGeometry.AffineFibrePointDimension`, preserving its complete signature.
The proof constructs the canonical residue-field comparison, tensor evaluation and its
kernel prime, and the affine open fibre chart. It verifies both projections, the range,
and the marked point. It then uses `Algebra.Presentation.baseChange` and its quotient
isomorphism for the presentation, and `AlgebraicGeometry.dimension_at_point_components`
for finite point dimension. Three proved private helpers handle residue-field transport
and dimension under an open immersion. Updated the node's proof to this argument.

Validation: `lcompile.py` compiled the complete module cleanly in 7.6 seconds
(exit 0). The original public theorem signature and all public imports are unchanged;
all lines are at most 100 characters. LeanFinder, Loogle and grep searches found the
existing affine pullback APIs; the library search also found the same presentation
quotient construction in `RelativeGlobalCompleteIntersectionBaseChange`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.affine_fibre_point_dimension`
(node `lem-trf-affine-fibre-point-dimension`). No holes added or split off.
There are zero remaining `sorry` proofs in the delivered module.

## No longer needed

Removed the unused private import
`WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`.
The proof no longer uses `lem-weil-pbc-spec-field-point-residue-field`: the existing
Mathlib leaf `lem-weil-pbc-spec-residue-field-identification` supplies the required
canonical affine residue-field isomorphism, and the existing Mathlib leaf
`lem-weil-pbc-prime-residue-field-algebra` supplies its kernel calculation.
No auxiliary morphism from Spec κ(q) is needed to identify the marked point: use
contraction and injectivity of the fibre projection. No tensor-factor swap is needed:
the affine pullback and base-changed presentation already use κ(p) ⊗_R A.
No whole module is withdrawn; other consumers may still need the removed import.
All remaining original proof-dependency nodes are retained and used.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false statement was found.
The planned tensor swaps and field-valued-point detour are unnecessary with the
existing Mathlib interfaces. The proof follows the same affine fibre calculation
and preserves the unit route. No definition, target, or consumer interface changes.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
