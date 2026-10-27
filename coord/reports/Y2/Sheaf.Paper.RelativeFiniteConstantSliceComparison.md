## What changed

Added two strictly smaller admitted interface lemmas and proved
`AlgebraicGeometry.Scheme.relativeFiniteConstantSliceComparison` by composing them.
`relativeFiniteModelSliceEquivalence` handles arbitrary module pairs under the
small-site slice equivalence; `relativeFiniteConstantModelIdentification` identifies
the transported inverse-image constant module with the native constant coefficient
module. The item imports these two modules. All three modules compile together.

## Proved and sorry left

The item theorem `relativeFiniteConstantSliceComparison` is proved. Two strictly
smaller obligations remain as `sorry`:

- `AlgebraicGeometry.Scheme.relativeFiniteModelSliceEquivalence`, node
  `lem-weil-pbc-relative-finite-model-slice-equivalence`;
- `AlgebraicGeometry.Scheme.relativeFiniteConstantModelIdentification`, node
  `lem-weil-pbc-relative-finite-constant-model-identification`.

Thus one existing hole is closed and two lower holes are split off.

## No longer needed

No original public import was removed. The parent proof uses only the two new
lemmas directly; its former direct proof-plan dependencies are represented through
their nodes and are not imported again by the item.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the site-equivalence transport and the
constant-sheaf universal-property comparison into one large argument. These are
independent strictly simpler obligations, so the item is reduced to their genuine
composition. No statement signature was changed.

## New nodes

`lem-weil-pbc-relative-finite-model-slice-equivalence` is stated in
`lean/Sheaf/Paper/RelativeFiniteModelSliceEquivalence.lean`; its change record is
not needed because no existing declaration or definition changed.

`lem-weil-pbc-relative-finite-constant-model-identification` is stated in
`lean/Sheaf/Paper/RelativeFiniteConstantModelIdentification.lean`; its change record
is not needed because no existing declaration or definition changed.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
