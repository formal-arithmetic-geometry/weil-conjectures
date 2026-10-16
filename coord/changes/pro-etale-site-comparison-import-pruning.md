# AlgebraicGeometry.Scheme.proEtaleSiteComparison

## Reason

The finite-limit proof uses only the canonical comparison definitions, ModuleCat's
Abelian instance, and the generic filtered-colimit and sheaf pullback APIs. The former
public imports of `ProEtaleDerivedCategory` and `RingedSiteModules` were unused by all
three declarations in this module and unnecessarily exposed unrelated declarations to
its downstream importers. They are removed as a proof-interface pruning change.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
```

## New

Neither import is present. The retained public imports are
`WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` and
`Mathlib.Algebra.Category.ModuleCat.AB`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishingAux | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonSections | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | retained comparison API |
| Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence | unclaimed | retained comparison API |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | retained comparison API |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | retained comparison API |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | retained comparison API |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | unclaimed | retained comparison API |

## Status

landed 20261016T061028-L-327983 2026-10-16 (merge of deliver/U4/Sheaf.AlgebraicGeometry.ProEtaleSiteComparison)
