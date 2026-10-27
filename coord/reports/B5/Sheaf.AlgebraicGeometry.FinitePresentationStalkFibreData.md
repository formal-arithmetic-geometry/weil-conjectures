## What changed

Filled `AlgebraicGeometry.Scheme.Hom.exists_finitePresentation_stalk_fibre_data`
without changing its statement. Added three proved private helpers in the item module:
`quotient_extendScalars`, `stalk_localization_model`, and `pullback_quotient`.
Added the proof-only import `Mathlib.LinearAlgebra.TensorProduct.Quotient`.

The proof follows the existing four-step plan. Restrict to affine neighbourhoods and
transport the existing finite-presentation localization model through `resLEStalkMap`.
Use the source-stalk presentation for the finite free maps. Use the fibre-stalk quotient
for theta. Mathlib's `quotTensorEquivQuotSMul`, followed by tensor transport along theta
and the inverse tensor-pullback stalk comparison, constructs eta. Its scalar and germ
formulas are proved explicitly; the latter uses the section normalization of the
upstream pullback adjunction. The arbitrary-point equality is handled by substitution
in a general private helper, preserving the actual stalk identification.

Validation: the full item compiled through `lcompile.py` with no errors or warnings
in 16.3 seconds, below the 60-second limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.exists_finitePresentation_stalk_fibre_data`
(node `lem-trf-finite-presentation-stalk-fibre-data`).

Holes closed: 1. Holes added: 0. Sorries left in delivered files: none.
No decomposition or new theorem with a postponed proof.

## No longer needed

None. All four mathematical proof dependencies remain used. No imports, modules,
DAG nodes, unit steps, or upstream declarations are withdrawn. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The elementary tensor-quotient construction planned in
step 4 is already available as Mathlib's `TensorProduct.quotTensorEquivQuotSMul`.
Its inverse sends the class of m to 1 tensor m; the tensor balancing relation proves
the required semilinearity, including zero modules and zero free ranks.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
