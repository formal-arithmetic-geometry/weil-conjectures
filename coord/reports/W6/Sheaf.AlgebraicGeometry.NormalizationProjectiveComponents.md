## What changed

Proved `AlgebraicGeometry.normalization_projective_components` with its full original
signature unchanged. Reused the proved source normalization APIs for finiteness,
surjectivity, integral structure, normal stalks and dimension; the proved finite-family
copairing API handles the empty family as well. Transported the standard coproduct
along its unique comparison isomorphism to the specified colimit. Constructed the
component maps to the reduction using the nilradical kernel inclusion and the
closed-immersion lift, then proved the factorization by colimit hom-ext.

Added proof imports of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`. Updated the item's
proof plan, proof dependencies and origin to this implementation. No statement,
definition, public import or consumer changed.

Validation: single-file lcompile succeeds with no warnings. Delivery preflight
checks and their result are recorded by deliver3.py.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.normalization_projective_components`
(node `lem-weil-pbc-normalization-projective-components`).
Added 0 holes; split off 0 theorems. No `sorry` remains in the delivered module.
The proof uses the existing stated theorem
`AlgebraicGeometry.finite_over_projective_affineLocally`, whose proof is still
`sorry` in its own unchanged module; this delivery does not claim to close it.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.ReducedSourceFactors`: the proved source ideal-kernel criterion
  and Mathlib closed-immersion lift construct the needed factorization directly.
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`: the canonical
  source projectivity API already supplies properness.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`: the component schemes
  and inclusions are supplied in the hypotheses; there is no need to construct
  their reduced induced structures.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: already publicly available
  through the canonical projectivity module; no separate proof import is needed.

Removed proof dependencies:

- `lem-kun-projective-implies-proper`: use the canonical source instance instead
  of the additional Sheaf conjunction.
- `lem-weil-pbc-reduced-induced-closed-subscheme`: component data are given;
  the reduction factorization uses the explicit closed-immersion lift.
- `lem-sc-scheme-sober`, `lem-sc-integral-function-field-affine-fraction`,
  `def-fin-normalization-extension`: the proved integral normalization and normal
  stalk APIs replace the planned generic-point and affine-chart construction.
- `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`: replaced by the
  proved source kernel-support criterion followed by the Mathlib lift.

Corresponding unused `tool_uses` entries were removed. Statement dependencies and
all unit realizations remain unchanged; a removed proof dependency may still be
needed elsewhere, so this report does not claim global unreachability.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned chart-by-chart normality and
finite-coproduct induction have already been implemented in the source library.
The provided component data also make reconstruction and uniqueness of reduced
induced component subschemes unnecessary in this proof. The reduction factorization
is a short application of existing proved source and Mathlib APIs.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
