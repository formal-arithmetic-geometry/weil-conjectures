# Sheaf.Paper.IntegralResiduePullFlatModel proof interface

## Reason

The direct mate proof was split after its final specialization exceeded the heartbeat
budget. The replacement proof delegates the comparison equality to the new named theorem
`residueExchangePull_flatModel_comparison` and therefore no longer needs the private cached
instances, mate helpers, ordinary-unit import, or derived-mate import. The public target
statement and all public declarations used by importers remain unchanged.

## Old

```lean
public import Sheaf.Paper.IntegralResiduePullSquareData
import Sheaf.Paper.IntegralResiduePullbackPreservesFlat
import Sheaf.Paper.IntegralResiduePullOrdinaryUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
```

The old file also contained private declarations `cachedProofInstance1` through
`cachedProofInstance12`, `exactSquareFac`, `exactSquareFacInv`, `liftedSquareFac`,
`exactLeftSquareFac`, `transportedUnitFac`, `mixedDerivedUnitFac`, `mateModel`,
`naturalOrdinaryFac`, `reduction_unit_fac`, and `restrict_pull_fac`.

## New

```lean
public import Sheaf.Paper.IntegralResiduePullSquareData
import Sheaf.Paper.IntegralResiduePullbackPreservesFlat
import Sheaf.Paper.IntegralResiduePullFlatModelComparison
```

The public theorem `residueExchangePull_flatModel` retains its exact old signature. The
private direct-mate declarations are removed; the comparison is supplied by the new
publicly named theorem in `IntegralResiduePullFlatModelComparison`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | Public target theorem unchanged; proof imports the item module as before. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | No declaration usage; unchanged. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | No declaration usage; unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No declaration usage; unchanged. |
| TargetsCheck | unclaimed | No declaration usage; unchanged. |
| WeilConjectures | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No declaration usage; unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No declaration usage; unchanged. |

## Status

landed 20261017T051253-L-3360999 2026-10-17 (merge of deliver/D4/Sheaf.Paper.IntegralResiduePullFlatModel)
