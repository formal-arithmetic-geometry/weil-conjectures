# WeilConjectures.sfIntegralLocalizationConstruction

## Reason

The new combining proof imports the ordinary-recollement interface. Its completed
coefficient instances introduce a stuck universe constraint when elaborating the
supported record and finite Tor projections. Use the same local elaboration setup
as SfIntegralOrdinaryRecollementRealization and its existing consumers: disable the
two general completed-coefficient instances and allow a larger instance search.
The original theorem and every existing public definition retain their signatures.
No target statement or definition used by a target changes.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

## New

```lean
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

The new comparison module uses this same setup. New declarations are the
SfIntegralLocalizationComparisonData record, sfIntegralLocalizationComparisons,
and sfPositiveFiniteLocalizationConstruction, each owned by its new node.
No existing signature, public import, definition body or instance body changes.

## Users

`tools/downstream.py Sheaf.Paper.SfIntegralLocalizationConstruction --uses
sfIntegralLocalizationConstruction` found 40 transitive importers and only one
external declaration user, SfLocalizationAllStages. No consumer adaptation is
necessary because the theorem and all existing data types keep their signatures.
New instance removals are used for this file's elaboration, just as in the existing
ordinary-recollement module. The reader checks command effects independently.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | S3 | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | N2 | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | R8 | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | A4 | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | Unchanged statements and bodies; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Unchanged statements and bodies; no adaptation. |

## Status

landed 20261025T164813-L-1086400 2026-10-25 (merge of deliver/Y2/Sheaf.Paper.SfIntegralLocalizationConstruction)
