# AlgebraicGeometry.ProEtale.CoefficientCompatibility proof options

## Reason

The delivered composition proof needs local reducibility controls for large canonical
functors. The static stage-3 check treats the local `attribute` command as a possible
consumer-visible change, so this record documents it. No public declaration signature,
definition, visibility, or public import changes.

## Old

The module had no local irreducibility attribute before the retained composition proof.
It also imported `Sheaf.AlgebraicGeometry.EtaleSumStalks`,
`Sheaf.Paper.AcyclicFlatProperCoefficientModel`, and
`Sheaf.Paper.RefinementCoefficientMate` for the original holed proof plan.

## New

The proof module adds the following local command:

```lean
attribute [local irreducible] etaleCoefficientMap etaleCompositor
  siteRefinement siteCompositor compositionSiteBoundary proEtaleCoefficientMap
  scalarPresentation supportPresentation transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison pbcComparisonReduction pbcFixedScalarExtension
```

It removes the three proof-only imports listed above. The local attribute affects only
elaboration in this module and is not exported. All named declarations retain their
exact old signatures and meanings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |
| Sheaf.Paper.VerdierExchange | not queried; unchanged | Existing public declarations retain their signatures and meanings; no adaptation. |

No consumer uses the local proof options or the removed imports as an API.

## Status

landed 20261019T231400-L-580645 2026-10-19 (merge of deliver/U4/Sheaf.Paper.EtaleProEtaleCoefficientCompatibility)
