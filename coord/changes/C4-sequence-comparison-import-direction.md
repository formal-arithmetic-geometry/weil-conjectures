# IntegralComparisonSequenceSystems import direction

## Reason

The sequence-site definitions are prerequisites of the normalized integral pullback
realization. Their public import of IntegralPullbackComposition, which depends on
IntegralPullbackSystemComparison, prevents using the realization to prove this item.
No declaration in IntegralComparisonSequenceSystems references the composition API.
Remove this unused re-export to restore the mathematical dependency direction.

## Old

```lean
public import Sheaf.Paper.IntegralPullbackComposition
```

## New

The unused import is removed. Every existing declaration keeps its signature,
visibility and construction. Local proof transparency settings prevent repeated
unfolding of chosen scalar models; they have no exported effect.
The ordinary scalar/pullback uniqueness proof now eliminates its existence theorem
with `obtain` instead of repeatedly unfolding a chosen witness. The private unary
whiskering full-faithfulness proof uses a single `FullyFaithful` record. Existing
public definitions and theorem signatures are unchanged. The repaired module compiled
in 38.5 seconds, with no holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | A4 | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | R6 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.CompletedPullbackTensorComparison | J6 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.EffectiveQuotientModelDescent | unclaimed | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | X7 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | U4 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.QuotientSystemMixedCoherence | U4 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.SequenceScalarGeneratorInterchange | V3 | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Local sequence API unchanged; does not use the composition API. |
| Sheaf.Paper.SystemOperationExchangeRealization | G2 | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels | unclaimed | Local sequence API unchanged; does not use the composition API. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | All local declarations retain signatures and bodies; imports the composition API independently. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Local sequence API unchanged; does not use the composition API. |

The complete transitive downstream list and textual uses were checked with
`tools/downstream.py Sheaf.Paper.IntegralComparisonSequenceSystems --uses
integralPullbackComposition`. Removing the unused re-export changes none of the
sequence constructions or target meanings. No source-library module is edited.

## Status

landed 20261025T201544-L-2576286 2026-10-25 (merge of deliver/C4/Sheaf.Paper.IntegralPullbackSystemComparison)
