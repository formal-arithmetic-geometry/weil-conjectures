# Coefficient scalar foundation module ownership

## Reason

After profiling and local irreducibility improvements, the assigned module still
compiled in 62–73 seconds even when Lean reported no errors. The session brief
permits splitting a self-contained part after these improvements. Move the
existing prefix, through `coefficientScalarTensorIso`, verbatim into
`Sheaf.Paper.CoefficientSystemScalarCalculus`. Keep the public declaration names,
statements, universe variables, data bodies and attributes unchanged. The
original module publicly imports the new foundation and retains all its old
public imports. This is a module-ownership change, with no change to the exported
mathematical interface. Replay the prefix's local proof settings in the original
module so its remaining declarations elaborate in the same local environment.

Three existing definition nodes now point at the new owner:
`def-sfb-abelian-tower-kinjective-resolutions`,
`def-pur-coefficient-base-change-hom`, and
`def-sf-finite-reduction-computation`. The two original declaration inventories
(`lem-coef-derived-system-evaluation-calculus`, `def-coef-derived-system-calculus-data`)
keep the moved names as declarations re-exported by the original module, so every
moved declaration keeps its recording node (independent review, 2026-10-27). No node
statement changes.

## Old

The original module directly declared the prefix starting with
`coefficientTowerSections` and ending with `coefficientScalarTensorIso`.
It had all the public imports retained in the delivered original module except
for the following new re-export.

## New

The prefix is verbatim in `lean/Sheaf/Paper/CoefficientSystemScalarCalculus.lean`.
The original module adds exactly this public re-export:

```lean
public import Sheaf.Paper.CoefficientSystemScalarCalculus
```

Every existing declaration keeps its original full signature and definition body.
The new module closes the original namespaces; the original module reopens the
same namespaces for the remaining declarations. No public declaration is removed
from the environment available to an importer of the original module.

## Users

The direct importers of `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` keep the
same exported declaration environment and need no source adaptations. Their
complete list is in the table below. No existing module other than the assigned item
is edited. No shared definition or statement is changed, so there is no forced
adaptation. The independent reader should check the declaration-type inventory
and the public re-export as a module split.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | C2 | Publicly re-export the unchanged scalar foundation; prove the ordinary evaluation comparison. |
| Sheaf.Paper.CoefficientSystemScalarCalculus | C2, new file | Own the unchanged scalar prefix. |
| Sheaf.Algebra.Homology.FlatScalarEvaluationModel | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Algebra.Homology.ScalarHomComparisonTower | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Algebra.Homology.ScalarHomDerivedSquareCoherence | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CoefOpenTensorEvaluationData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CoefficientExtensionReductionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CoefficientExtensionReductionModel | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientTransition | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | G2 | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportNativeSystemEvaluation | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationCoordinates | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CompletionUnitModels | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CondensedCompositorRealization | Z8 | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | M2 | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.EffectiveQuotientModelDescent | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.FiniteExpressionReductionComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.FiniteRationalDerivedOperations | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralComparisonSystemData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralMappingLimitProjections | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralOperationRoosEffectivity | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisonModels | N4 | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | N3 | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralStrictReductionModel | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.NormalizedArithmeticInterpolation | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PodCompletionReindexModels | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PodCompletionUnitScalarIntertwining | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PointSystemInsertionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PrimitiveCounitComparisonModels | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PrimitiveCounitEvaluation | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PurReductionLimitShiftData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.PurSequenceAdjointResolutionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportStrictReductionComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportStrictReductionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportStrictReductionGamma | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.RingedRestrictionStrictLimitCoherence | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.SequenceKInjectiveComparisonShifts | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.SfAmbientIntegralDirectImage | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnitData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.StrictReductionPresentationMap | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.SystemScalarTransitionComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.Paper.ZlFiniteIntegralFibreReconstruction | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionDefinitions | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenQuotientKoszulCompleteness | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenQuotientKoszulModels | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | Same exported names and signatures; no adaptation. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | unclaimed | Same exported names and signatures; no adaptation. |

## Status

landed 20261027T134955-L-3651497 2026-10-27 (merge of deliver/C2/Sheaf.Paper.CoefDerivedSystemEvaluationCalculus)
