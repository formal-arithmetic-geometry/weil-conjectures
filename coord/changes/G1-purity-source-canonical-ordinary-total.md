# WeilConjectures.RationalSmoothPurityCanonical.ordinaryTotal

## Reason

The new proof of tensorAugmentation_isIso repeatedly compares the manually
expanded signed total tensor with coefficientTotalTensor, including its monoidal
and zero-preservation dictionaries. Profiling showed expensive kernel conversions
in both strict normalization and the final mapped augmentation. Reuse the existing
canonical coefficientTotalTensor definition directly. This is the same ordinary,
uncompleted signed direct-sum total tensor, with the same objects, maps,
differential and type. No hypothesis, comparison formula or mathematical meaning
changes. No target statement changes.

The remaining proof changes use scoped local reducibility settings and proved
private helpers; none changes a consumer's interface or unfolding rules.

## Old

```lean
def ordinaryTotal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    CochainComplex (integralTowerModules l E T) ℤ ×
      CochainComplex (integralTowerModules l E T) ℤ ⥤
        CochainComplex (integralTowerModules l E T) ℤ :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor T
    (completedIntegralCommRingSheafUnrestricted l E T)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
```

## New

```lean
def ordinaryTotal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    CochainComplex (integralTowerModules l E T) ℤ ×
      CochainComplex (integralTowerModules l E T) ℤ ⥤
        CochainComplex (integralTowerModules l E T) ℤ :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T)
    (completedIntegralCommRingSheafUnrestricted l E T)
```

## Users

The table includes the full downstream module list from
`tools/downstream.py Sheaf.Paper.PuritySourceTransports --uses ordinaryTotal`.
The only declaration-name users are this item and
`Sheaf.SecSmoothPurity.RationalPurityLineComparisons`.
Every existing signature and public import is preserved. The ten direct importers and the explicit indirect ordinaryTotal user
all pass against the changed item within the per-file limit; their unchanged
test copies have been removed from the delivery sandbox. No forced adaptation is needed. The live library received E9's trace-coherence
subdivision while these checks ran; the explicit user is now the unchanged
RationalPurityLineComparisons module, which passes against this definition in
27.3 seconds. The obsolete pre-subdivision test copy is not delivered.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.AdmissibleCupCoefficientPassages` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateCommonComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateCompletedComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateComplexComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateNaturalityLaws` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateOrdinaryNaturality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateScalarComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalTateScalarNaturality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationCore` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationShift` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | C4 | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FieldOrientedExchangeSquares` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteFirstRootChart` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FinitePositiveChartFrameExt` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FinitePositiveChartRecursion` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FinitePositiveRootChartPower` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FinitePositiveRootCharts` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionPositiveLineComparison` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionReassociation` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorFactors` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorPurity` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorSource` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteReductionThetaFactor` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteRootTensorPresentation` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteSignedTwistProducts` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTateSourceStructuralCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorFixedComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorLineChartReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorPresentationReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorPullbackCompositionReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorPullbackTensorReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftFirst` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftSecond` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorSignedReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FiniteTensorSymmetryCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactIntegralNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactRationalNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceMate` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceNaturality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralOrientedExchangeSquares` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralPurityComparisonCocycles` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralPurityCounitReduction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.IteratedPurityScalarPasting` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientSquare` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupNormalizedScalars` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupOperationComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupTensorComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTrace` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTraceCommonStage` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTraceData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedSmoothOrientationUnits` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientationFiniteCoefficientTwists` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientationFiniteReductionTwists` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientationPerfectLines` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.PairingData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.PodMixedSupportCupProduct` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.PurityOrientationDatum` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | G1 | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpointData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpoints` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityLocalizedFamilyData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | N4 | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.RationalizationOrientedExchangeSquare` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientation` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationDatum` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationFamily` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationStageCompatibility` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | H2 | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOrientationCoefficientFamily` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOrientationPuritySquares` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOrientationStageExchange` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothOrientedExchangeComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.SpecifiedIntegralUnitOrientation` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedNormalization` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTraceCanonicalIntegral` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTraceOrientationUniqueness` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparison` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TowerTraceScalarCounit` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | J3 | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityLineComparisons` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same signed total tensor by definitional equality; no adaptation. |

## Status

landed 20261027T034645-L-3671325 2026-10-27 (merge of deliver/G1/Sheaf.Paper.PuritySourceTransports)
