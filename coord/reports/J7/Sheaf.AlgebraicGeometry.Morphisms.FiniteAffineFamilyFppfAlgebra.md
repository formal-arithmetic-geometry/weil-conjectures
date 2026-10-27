## What changed

Proved `AlgebraicGeometry.finiteAffineFamily_fppfAlgebra` in the assigned module,
with its signature and all existing public imports unchanged. The proof uses only
Mathlib declarations already available through those imports. Coproduct uniqueness
proves both coordinate comparisons and the triangle identity. Source locality gives
flatness, local finite presentation and local finite type; cancellation across
`sigmaSpec` transfers these to spectra of the product ring maps. The affine
criteria give the algebraic conclusions. Joint surjectivity supplies explicit
preimages, and faithful-flat injectivity handles the empty family.

Updated the assigned node's proof, proof dependencies and proof origin to match.
No other existing module or node is changed.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.finiteAffineFamily_fppfAlgebra`
(node `lem-a1-finite-affine-family-fppf-algebra`). No holes remain in the module;
no holes were added and no intermediate statements were split off.

## No longer needed

No imports were added or removed. The proof no longer needs the following planned
proof dependencies:

- `lem-weil-pbc-finite-product-flat-modules`: source locality gives coproduct flatness,
  and the finite coproduct isomorphism transfers it to the product spectrum.
- `lem-weil-pbc-lft-pointwise-criterion`: the source-locality coproduct lemma supplies
  local finite type directly from the affine component maps.
- `lem-weil-pbc-faithfully-flat-universally-injective`: injectivity of the faithfully
  flat ring map directly implies the empty-family conclusion.
- `def-weil-pbc-flat-ring-map` is no longer a separate proof dependency; it remains
  a statement dependency and is used through the affine flatness criterion.

These are existing Mathlib leaves, so no separate Sheaf module is withdrawn. No
unit realization is bypassed and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan's finite-product module-flatness argument
and tensor-product argument for the empty family were unnecessary: existing
coproduct locality and faithful-flat injectivity suffice. Empty families, zero
factors and one-element families require no additional hypotheses. The existing
node's historical blueprint ancestry is preserved; the current unit's realized
statement and proof steps are unchanged.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
