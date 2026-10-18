## What changed

Proved `AlgebraicGeometry.smooth_and_geometricallyReduced_of_geonormal_dim_le_one`
in `Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth`, with its signature unchanged.
For each field extension the base change is locally Noetherian, has dimension at
most one, and is regular by `IsRegular.of_isIntegrallyClosed_stalk`. Apply the
stated geometric regularity/smoothness criterion. Reducedness follows directly
from the domain stalks; connected base changes are integral and hence irreducible.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension` and used
`topologicalKrullDim_pullback_eq_of_field`, a closed declaration already audited
under `lem-pc-dim-base-change`. This directly supplies the scheme dimension
comparison that the original plan reconstructed chart by chart. The item's DAG
proof and proof dependencies now follow this argument. The unit's statement and
realized proof steps are unchanged. No definitions or other modules change. The final module compiles cleanly in 3.2 seconds
through lcompile.py, without warnings. Every changed Lean line is within 100 columns.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.smooth_and_geometricallyReduced_of_geonormal_dim_le_one`
(node `lem-weil-pbc-geonormal-dim-one-smooth`).
Added 0 holes; no `sorry` remains in the delivered module.
The proof still uses the stated
`smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange`; its existing
hole is not a new hole of this delivery.

## No longer needed

Removed direct imports `Mathlib.RingTheory.DiscreteValuationRing.Basic` and
`Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`.

The proof no longer directly needs these planned dependencies:
- `lem-weil-pbc-fibre-product-affine-spectra` and `def-weil-open-immersion`:
  the existing scheme base-change dimension theorem packages the affine charts.
- `lem-weil-pbc-dimension-preserved-field-extension` and its module
  `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`: replaced here by
  the audited source-library declaration of `lem-pc-dim-base-change`.
- `lem-sc-scheme-stalk-dimension-generalization-chains`,
  `def-sc-discrete-valuation-ring`, and `def-weil-regular-scheme`: the existing
  `IsRegular.of_isIntegrallyClosed_stalk` packages the stalk dimension and
  field/DVR regularity argument; its inferred local Noetherianity is supplied
  explicitly. These nodes may still be needed by other consumers or internally
  by the source-library proofs; no global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but duplicates existing source-library
results. In particular `topologicalKrullDim_pullback_eq_of_field` applies to every
scheme locally of finite type over an arbitrary field, and the normal-stalk
regularity theorem handles dimension zero and the empty scheme. QuasiCompact is
not needed by this proof; the original signature is preserved.

Read the source proofs at Properties 0BX2, Varieties 038X, and the normal-to-smooth
paragraph of Varieties 0GK5. Checked that no perfect-field or connectedness
assumption is used for smoothness, and nonemptiness enters only through
ConnectedSpace in the final clause. No new nodes or statement changes.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
