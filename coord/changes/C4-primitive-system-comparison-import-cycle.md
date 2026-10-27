# IntegralComparisonSequenceSystems import dependencies

## Reason

The sequence-site construction does not use any declaration from integral pullback
composition, but publicly imported that consumer. Reusing its primitive comparison
in IntegralPullbackSystemComparison exposed this cycle. Replace the unnecessary
composition import by the two lower interfaces its constructions use. The module
is unclaimed. Preserve all declarations, signatures, attributes and proof bodies.

## Old

```lean
public import Sheaf.Paper.IntegralPullbackComposition
```

## New

```lean
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralFinitePullbackComposition
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Replace an unused consumer import by lower dependencies. |
| Sheaf.Paper.IntegralPullbackSystemComparison | C4 | New proof imports the primitive coherent comparison. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | A4 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | R6 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.EffectiveQuotientModelDescent | F5 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | J6 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | U4 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.SequenceScalarGeneratorInterchange | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No use of the removed composition declarations; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | No use of the removed composition declarations; no adaptation. |

## Status

landed 20261025T201544-L-2576286 2026-10-25 (merge of deliver/C4/Sheaf.Paper.IntegralPullbackSystemComparison)
