## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/FixSiteOpenExchange.lean`.
The module uses the ordinary finite-constant-coefficient module categories on the
small etale and pro-etale sites.  It defines the derived extension comparison
`fixSiteOpenComparison`, the inverse-image comparison `fixSitePullbackComparison`
with the node's orientation `rho_u : u_proet^{-1} N_V -> N_T u_et^{-1}`, and the
chosen-square pullback witness `fixSiteIsPullback`.  The theorem
`fixSiteOpenComparison_unit_normalization` records the inverse-unit normalization
of `c_j`; `fixSiteOpenExchange` states the requested equality with `sorry`.
All three theorem proofs are intentionally postponed at stage 2.

The Lean rendering of the item hypotheses is explicit in the theorem signature:
`Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`; schemes `U' U X' X`; maps
`gU`, `j'`, `j`, `g`; `[IsOpenImmersion j]` and `[IsOpenImmersion j']`; the
cartesian open-immersion datum `sq : OpenImmersionSquare gU j' j g`; and
`K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat Λ))`.
No hypothesis on `g` is added.  The left composite is rendered by
`fixSiteOpenComparison.hom` (the map `g_proet^{-1}(c_j)`), the canonical
`ordinaryOpenExtensionBaseChangeIso.hom` (the map `e_j^proet`), and the map of
`fixSitePullbackComparison.hom` under `j'_!` (the map `j'_!(rho_h)`).  The right
composite is `fixSitePullbackComparison.hom` for `g` (`rho_g`), followed by the
map under `N_X'` of `Etale.extensionZeroBaseChangeDerivedPlusIso.hom` (`e_j^et`),
and `fixSiteOpenComparison.hom` for `j'` (`c_j'`).  The source and target are
therefore the same objects in the ordinary derived category on `X'`'s pro-etale
site.  Naturality in `K` is inherited from the natural-isomorphism maps and the
canonical derived base-change isomorphism; the statement's proof docstring lists
all six proof steps and the identity, empty-open, zero-complex, and zero-ring
edge cases.

The dependency declarations read were:

- `def-weil-pbc-proetale-modules`: `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` in `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`.
- `def-weil-pbc-proetale-operations`: `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback` in `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `def-weil-pbc-adjunction-mate`: Mathlib `CategoryTheory.mateEquiv` in `Mathlib/CategoryTheory/Adjunction/Mates.lean`.
- `def-cbc-open-immersion-square`: `AlgebraicGeometry.OpenImmersionSquare` in `Sheaf.AlgebraicGeometry.OpenImmersionSquare`.
- `def-weil-pbc-derived-categories`: `AlgebraicGeometry.Etale.DerivedCategoryModule` / `DerivedCategory.Plus` in `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `def-weil-pbc-site-comparison-morphism`: `AlgebraicGeometry.Scheme.proEtaleSiteComparison` in `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `lem-weil-pbc-comparison-pullback`: `AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent` in `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `lem-weil-pbc-extension-by-zero-exact`: `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` in `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `lem-cbc-proetale-extension-zero`: `AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` in `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `lem-cbc-proetale-extension-zero-comparison`: `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence` in `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `cor-cbc-derived-extension-zero-base-change`: `AlgebraicGeometry.Etale.extensionZeroBaseChangeDerivedPlusIso` in `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`.
- `lem-cbc-proetale-extension-zero-base-change`: repaired below.

The ordinary pro-etale base-change map needed by the item could not be applied
through the recorded `StrictTower.singleBeta`: its `Modules Λ X` categories are
strict-tower ringed-site categories, while this item is stated in
`Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`.  The delivery therefore includes
the permitted dependency repair module
`lean/Sheaf/AlgebraicGeometry/ProEtaleDerivedExtensionZeroBaseChange.lean`.
It defines `ordinaryOpenExtensionBaseChangeIso` as the derived image of the
inverse mate of the canonical `ProEtale.baseChangeMap`, using the chosen
`IsPullback` witness.  This is the same canonical map and orientation as the
dependency statement, with no arbitrary choice.  The copied dependency node
has only its `lean` record changed and its `lean.note` records this interface
repair.

Edge cases checked against the statement and source are the identity square,
an empty open, the zero complex, the zero coefficient ring, and arbitrary `g`;
these are explicitly retained in the theorem docstring and no case is excluded
by a typeclass hypothesis.

Searches made:

- `msearch.py ... leanfinder "ordinary pro-etale extension by zero base change comparison with etale site comparison"`: eight Mathlib hits, all ring-theoretic etale/base-change declarations; no site-comparison declaration.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, AlgebraicGeometry.ProEtale.baseChangeMap"`: zero hits; the service reported the project identifier as unknown.
- `msearch.py ... grep "proEtale.*baseChange|openImmersion.*Comparison" AlgebraicGeometry`: zero hits in Mathlib's AlgebraicGeometry subtree.
- `rg` over `WeilConjectures` and `lean/Sheaf`: found the canonical `ProEtale.baseChangeMap`, `comparisonUpperStarCompUpperStarIso`, `openImmersionLowerShriekComparisonUpperStarIso`, and the existing derived etale base-change declaration; no existing declaration of this item's normalized comparison theorem.
- The node's retained stage-1 search records were checked; the stray extra leanfinder entry from the returned split delivery was removed.

## Dependency modules

`lem-cbc-proetale-extension-zero-base-change` is repaired by
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange` because its
recorded `StrictTower.singleBeta` declaration has the wrong category interface
for the dependency's ordinary pro-etale notion.  The repair states that notion
using the canonical `ProEtale.baseChangeMap` mate and its derived map, with the
same finite commutative coefficient ring, open immersions, arbitrary commuting
bottom map, and chosen cartesian square.

## Second reading by Q07

I reread the copied item node and the final Lean module.  The finite commutative
ring, both open-immersion hypotheses, arbitrary `g`, chosen cartesian square,
and bounded-below etale input all appear in the theorem signature.  The left
side is exactly `j'_!(rho_h) . e_j^proet . g_proet^{-1}(c_j)` in composition order;
the right side is exactly `c_j' . N_X'(e_j^et) . rho_g`.  The normalization theorem
uses the etale open-adjunction unit, the comparison restriction isomorphism, and
the inverse-image comparison component, matching the node's specified inverse
unit formula.  The repaired dependency was reread to ensure its map is the
canonical inverse mate rather than a chosen or merely nonempty isomorphism.
No statement, hypothesis, or edge case was changed in this second reading.
