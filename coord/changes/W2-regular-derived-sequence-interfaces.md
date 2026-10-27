# Derived coefficient-sequence interfaces

## Reason

The proof profiles show repeated unfolding of derived evaluation and restriction
while checking component statements. Keep their existing construction bodies but
present these interfaces as reducible ordinary definitions. This unclaimed module
contains no holes. The change introduces no arbitrary data or new declaration.

## Old

The four declarations `coefficientSequenceDerived`,
`coefficientSequenceDerivedEvaluation`, `coefficientSequenceRestrictedDerived` and
`coefficientSequenceDerivedRestriction` were `noncomputable abbrev`.

## New

The same four declarations are `@[reducible] noncomputable def`, with signatures
and bodies verbatim. The derived categories still use `HasDerivedCategory.standard`.
Evaluation and restriction still descend their original exact ordinary functors
using `Functor.mapDerivedCategory`. Thus their mathematical meanings and all data
are definitionally identical. Definition-sensitive review is requested for reached
targets using them. No consumer source adaptations are needed.

A new proved private helper, `transition_presented`, transports the existing
`transition_generic` statement along three functor equalities. It leaves the
sectionwise characterization and uniqueness assertion intact. The concrete proof
passes its named evaluation and restriction functors with three `rfl` equalities,
so matching the conclusion does not expand concrete coefficient actions repeatedly.

The existing transition-existence proof now checks
`backward.isDefEq.respectTransparency` and its `types` variant. It first
instantiates the same general transition lemma in a named local fact and then
matches its conclusion to the concrete statement. These changes leave every
construction body unchanged, including existing generated proof constants.

## Users

Source scan refreshed 2026-10-26T08:59+00:00.
The import closure has 1697 modules; 65 mention the changed
declarations under the `tools/downstream.py --uses` criterion.
Statements, module actions and constructions remain definitionally equal.
No forced consumer edits are included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | J6 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefOpenTensorEvaluationData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientConstantTowerRoos` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientEnrichedGlobalShift` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionReductionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionRepresentativeRoos` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictDerivedComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictRepresentatives` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictTensorNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientReductionNaturalCochainComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientRingedSequenceSite` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientScalarCochainEvaluation` | E9 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientSequenceRoosModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportCoefficientTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportNativeSystemEvaluation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportNativeSystemTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedOpenTensorRepresentatives` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | E4 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitDerivedAdjunctionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitFiniteMateComparison` | J9 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitStrictQuotientModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralMappingLimitProjections` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralScalarTowerEffectivity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStrictReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedArithmeticInterpolation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PodIdentityReductionTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceComparisonTranspose` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceProjectionHomNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` | N3 | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientSystemMixedCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientSystemMixedCoherenceData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.RoosAdjunctionQuotientNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SequenceDerivedAssociativity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SequenceKInjectiveComparisonShifts` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.SfAmbientIntegralDirectImage` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionPullbackNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionScalarNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CoefHomTowerScalarModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrAugmentedReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenDvrAugmentedTowerComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenQuotientKoszulModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | unclaimed | definitionally identical data; no adaptation |

## Status

landed 20261026T102415-L-355579 2026-10-26 (merge of deliver/W2/Sheaf.Paper.IntegralOperationRoosEffectivity)
