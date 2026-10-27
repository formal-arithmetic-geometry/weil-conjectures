## What changed

Replaced the sole sorry in `WeilConjectures.pbc_proper_integral_ordinary_inputs`
with a complete assembly proof, retaining its signature verbatim. Its proved private
helpers establish residue annihilation, properness after base change, geometric fibre
bounds, exact coefficient-edge inputs with the uniquely normalized tensor-unit map,
effectivity of coefficient transport, both membership equivalences, uniform reduction
bounds, ordinary pullback membership and presentation-independent completion matching.
The proof uses the existing arithmetic, proper-preservation, stratified-perfect and
ordinary-pullback declarations, including their currently unproved dependencies.

The genuine remaining argument is the separate ambient theorem
`WeilConjectures.pbc_proper_integral_strict_model_comparison`, in its own module.
It concerns the normalized ordinary and completed strict-tower models for one arbitrary
morphism, without the proper square, arithmetic, membership or constructibility claims.
The main proof applies it twice and uses naturality to handle every presentation
isomorphism. It is a strictly smaller mathematical part of the original conjunction,
not that conjunction under another name.

Moved the thirteen original interfaces verbatim into `ProperIntegralOrdinaryData`,
publicly re-exported by the item, to avoid a circular import. No data, statement,
visibility, choice or instance body changed; only docstrings' owning blueprint labels.
The original theorem signature and all original public imports are unchanged.
The change record is `coord/changes/Q5-proper-integral-ordinary-data.md`.

## Proved and sorry left

Original hole closed by reduction:
`WeilConjectures.pbc_proper_integral_ordinary_inputs`
(node `lem-weil-pbc-proper-integral-ordinary-inputs`).

One hole added and still open:
`WeilConjectures.pbc_proper_integral_strict_model_comparison`
(node `lem-weil-pbc-proper-integral-strict-model-comparison`).
It has a complete sourced natural-language proof and its exact Lean statement in
its own module and node. There are zero holes in the item and zero holes in the
extracted data module. This is a one-to-one decomposition, not a net hole reduction
or an axiom-free proof of the original theorem. No existing dependency sorry was
closed or replaced. The private helpers are fully proved.

## No longer needed

Removed unused proof imports from the item:
`Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`,
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`,
`Sheaf.AlgebraicGeometry.DimensionExtension`,
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`,
`Sheaf.Paper.CompletedRlimFunctor`,
`WeilConjectures.Algebra.Homology.RoosComplex`, and
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
The last remains a proof import of the data module because its existing products
instance uses that theorem. The source Roos module and ringed pullback theory remain
needed by the separate ambient comparison. No module is withdrawn.

The item no longer needs the planned nodes
`lem-fin-finite-type-fibre-dimension-bound` and `lem-kun-dimension-extension`:
`topologicalKrullDim_pullback_le` bounds every field-point fibre by the already
assumed finite bound on X. Their proof-dependency edges have been removed.
The coefficient proof uses the projection-normalized `FourCorners` interfaces,
actual exact pullback and scalar-adjunction formulas, rather than importing
`lem-weil-pbc-profinite-coefficient-inverse-image`,
`lem-weil-pbc-site-pullback-abelian-exact` or
`def-weil-sheaf-of-modules-category` as separate proof dependencies.
The standard-quotient perfectness node is not used to prove the asserted arithmetic
clauses; the published adic datum already supplies its required structure.
These nodes may remain needed transitively elsewhere; no global deletion is claimed.

## Where the brief, the DAG or earlier work was wrong

The stated dependency interfaces do not themselves provide the normalized comparison
between these two actual coefficient presentations, whole strict towers, both Roos
coordinates and universal derived counits. The existing `IntegralRoosDerivedPullbackUnit`
interface assumes finite-type separated schemes over one common field, and the finite
stage whole-tower interfaces assume the morphism is an isomorphism. Neither applies
to the arbitrary morphisms of this statement. The ambient comparison records exactly
this missing part of original proof steps 5–7. Mathlib and library searches found no
matching theorem. This does not dispute the mathematical statement.

The planned two-step fibre dimension argument is unnecessary under the item's own
finite-dimensional X hypothesis. No unit-level route is changed.

## New nodes

`def-weil-pbc-proper-integral-ordinary-data` owns the thirteen unchanged normalized
interfaces moved from the item. It contains no new mathematical assertion and no hole.

`lem-weil-pbc-proper-integral-strict-model-comparison` states the ambient normalized
model comparison used twice by the item. Its proof plan follows the tensor balancing,
strict augmentation, exact-products Roos comparison and localization argument of
Bhatt--Scholze 6.5.9(4), Remark 6.8.15 and Stacks Tags 0941 and 099N(5).
The change record is `coord/changes/Q5-proper-integral-ordinary-data.md`.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
