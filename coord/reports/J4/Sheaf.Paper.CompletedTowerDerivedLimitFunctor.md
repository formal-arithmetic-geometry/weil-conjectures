## What changed

Filled the six theorem proofs in `Sheaf.Paper.CompletedTowerDerivedLimitFunctor`.
Strict towers obtain K-injective resolutions from
`reductionTower_isGrothendieckAbelian` and the source-library Grothendieck theorem.
Inverse limit is additive because it preserves binary products. The constant diagram
functor preserves limits and colimits, and hence is additive and exact.

Constructed the normalized constant-to-derived-limit unit by composing the ordinary
unit on complexes, the universal right-derived unit, and the exact constant functor's
localization comparison. Fully faithful precomposition with derived localization
provides its unique descent. This proves the existing representative formula exactly.

Triangulatedness comes from the source-library total-right-derived instances;
`Functor.rightDerivedUnique` proves comparison with any other universal derived pair.
For the Roos theorem, exact pro-etale countable products supply derived products, and
`completedRlim_roos` supplies the triangle with its canonical first arrow. The
`pbcModules`/`pbcTowers`/`pbcAdicCompletion` interfaces are definitionally the same
categories and coefficients used by the existing `completedRlim` construction.

All added imports are private proof imports. The proofs explicitly install the existing
`integralCoefficientAbSheafify.{u, 0}` and
`integralCoefficientAbLocallyBijective.{u, 0}` facts to fix sheafification universes. Existing signatures, public imports,
definitions, universes, and attributes are unchanged. No consumer adaptation is needed.

## Proved and sorry left

Closed all six existing holes:

- `AlgebraicGeometry.Scheme.completedTowers_hasKInjectiveResolutions`
- `AlgebraicGeometry.Scheme.completedTowerLimit_additive`
- `AlgebraicGeometry.Scheme.completedTowerConstant_exact`
- `AlgebraicGeometry.Scheme.completedConstantRlimUnit_exists`
- `AlgebraicGeometry.Scheme.completedTowerRlim_properties`
- `AlgebraicGeometry.Scheme.completedTowerRlim_roos`

No holes remain in the item and no holes are added elsewhere. No split-off statements.
The six-proof version compiled cleanly through `lcompile.py` in 16.1 seconds before
removing redundant trial imports; the delivery command validates the final import set
and checks declaration axioms.

## No longer needed

Removed redundant trial proof imports of
`Mathlib.CategoryTheory.Preadditive.LeftExact`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
The needed Grothendieck and triangulated declarations are public exports of
`CompletedRlimFunctor`; additivity uses the available binary-product criterion.
No original imports, nodes, or modules withdrawn. The existing proved `CompletedRlimFunctor`
provides the K-injective Roos computation, so duplicating that argument under the
`pbc` abbreviations is unnecessary. Its existing proof dependencies remain needed
through that module; no pruning of them is claimed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The module's docstrings point to `prop-weil-pbc-rlim-functoriality`, whose current Lean
attachment is `Sheaf.Paper.CompletedRlimFunctor`, not this older parallel interface.
That module already proves the generic construction and the stronger canonical-first-arrow
Roos theorem. This delivery reuses those results without changing either interface.
The constant-unit proof follows the existing docstring's localization argument.
No mathematical statement correction was needed.

Searches: the launcher's Lean Finder query on additive limit functors and K-injective
resolutions returned general Grothendieck/injective results; Loogle found
`CategoryTheory.Functor.rightDerivedUnique`; the Mathlib grep found
`Functor.preservesLimits_const` and `Functor.additive_of_preserves_binary_products`.
Local searches found the existing complete `CompletedRlimFunctor` proof.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
