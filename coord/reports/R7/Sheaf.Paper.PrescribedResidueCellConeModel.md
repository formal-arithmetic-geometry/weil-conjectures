## What changed

Proved `WeilConjectures.sf_prescribed_residue_cell_cone_model` in
`Sheaf.Paper.PrescribedResidueCellConeModel`, retaining its complete public statement
and all existing definitions. Private, proved helpers construct the complementary
cone splitting, identity-pair term identifications and normalized contraction,
zero-differential cohomology, restriction comparison, K-flatness and tensor model.
The prescribed cohomology splitting and natural generator bijection are reused.
The all-model top-map equality feeds Mathlib's distinguished-triangle isomorphism.

Added private proof imports for `SitePerfectModelRestriction`,
`BoundedFlatIndependentCoefficients`, `RingedKFlatSingleTensorComparison`,
`TensorColimitsIndependentCoefficients`, finite-biproduct preservation, complex
biproducts and the source flat/K-flat API. Updated the node proof and dependencies
to match the implementation. No public interfaces or source-library files changed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.sf_prescribed_residue_cell_cone_model`
(`lem-sf-prescribed-residue-cell-cone-model`). All clauses are proved, including
arbitrary slice restrictions, independent universes, every prescribed splitting,
the normalized contracting homotopy, the Tor interval and the equal-endpoint case.
Holes closed: 1. Holes added: 0. Sorries remaining in the item: none.
No split-off statements or new public declarations. Final single-file server compile
passed without errors or warnings in 38.3 seconds; the theorem signature was also
compared verbatim with the original and is unchanged.

## No longer needed

Removed private imports:
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`;
- `WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIso`;
- `Mathlib.CategoryTheory.Sites.CoverLifting`;
- `Mathlib.Algebra.Homology.BifunctorShift`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.

The last two are already available through the actual tensor-comparison dependency.
The first three are unnecessary because the statement already uses the slice site,
and the independent-universe exact restriction API handles it directly.

Removed proof dependencies `lem-weil-proetale-weakly-etale-localization`,
`lem-pur-localized-module-restriction-quasi-iso`, and
`lem-weil-pbc-site-constant-restriction`. The first two obsolete `tool_uses`
approvals were removed as well. The explicit tensor calculation uses the published
comparison API, so `def-pc-tensor-complex-sheaves` and
`def-pur-sheaf-tensor-product` are no longer direct proof dependencies.
No module is withdrawn: dependencies still used elsewhere remain in the library.

## Where the brief, the DAG or earlier work was wrong

The original restriction plan unnecessarily passed through the pro-etale-site
localization equivalence and a restriction lemma with unsuitable coefficient
universes. Exact restriction to the slice, with its existing independent-universe
derived comparison, proves precisely the stated restriction clause. The coordinate
K-flatness calculation is replaced by the existing bounded-above flat criterion;
the published K-flat/single comparison computes derived tensor without rebuilding it.
The statement and unit route remain unchanged. Zero ranks and the empty lower
interval are handled by zero objects and finite coproduct universal properties.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
