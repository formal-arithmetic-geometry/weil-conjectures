## What changed

Filled `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_composition` without changing its statement or any public definition. Added proved private categorical transport helpers, a computation of `compositionSiteBoundary`, and conversions between the existing finite-Tor domain predicates. The etale equation follows from the declared scalar refinement and composition equations. The pro-etale equation follows from the existing main compatibility declaration by naturality and cancellation. Added the private proof import `Sheaf.Paper.FiniteCompactSupportDomains` for the intermediate input's domain.

## Proved and sorry left

Closed 1 of the item's 3 original holes:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_composition`.
Added 0 holes and split off 0 statements. All new private helpers are proved.

The 2 holes retained are:

- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`.
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_sum`.

Both retain node `lem-sp-et-proet-coefficient-compatibility` and their existing statements and complete proof plans. The composition proof uses the first declaration as intended by stage 3; it does not assume its own conclusion.

## No longer needed

Removed unused private proof imports: `Sheaf.AlgebraicGeometry.EtaleSumStalks`, `Sheaf.Paper.AcyclicFlatProperCoefficientModel`, `Sheaf.Paper.RefinementCoefficientMate`, `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`, `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`, `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`, `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`, `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`, `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`, `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, `Sheaf.CategoryTheory.RingedSliceExtensionTensor`, `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, `Sheaf.Paper.ProperOpenCoefficientMate`, `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`. Their constituent calculations are supplied by the scalar-coherence theorem; the unchanged main and sum holes retain their documented plans.

The composition and refinement clauses do not need `lem-sp-finite-compact-site-coherence` (`Sheaf.Paper.FiniteCompactSiteCoherence`): their site comparisons are already defined by transport through the specified compact-support site comparisons. Naturality, functoriality and inverse cancellation suffice. Removed this dependency from Step 3 and `proof_deps`; it was not imported by the item. No module is withdrawn. No new modules are introduced.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to a separate finite compact-site coherence theorem is redundant for the actual `siteRefinement` and `siteCompositor` definitions. The existing etale scalar composition theorem is stated for chosen compactifications; the supplied compactifications require a real refinement/naturality transport argument, supplied here. The main square still requires identifying the recorded intrinsic reduction transport with its fixed-module mate; the sum clause still requires relating its derived scalar mate to the stated chain-level computation. Exploratory helpers for those two unfinished routes were removed from the delivery.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
