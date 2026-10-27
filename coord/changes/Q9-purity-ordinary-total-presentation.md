# WeilConjectures.RationalSmoothPurityCanonical.ordinaryTotal

## Reason

The descent proof repeatedly compares `coefficientTotalTensor` with the signed
ordinary total tensor appearing in `ProEtaleTensorModel.representative`. Both unfold
to `Functor.uncurry.obj` of the same `map₂HomologicalComplex` applied to the curried
sheaf tensor. Use the latter presentation directly, sharing the model's expression.
The new declaration also gives the functor type explicitly and uses `def` instead
of `abbrev`, so elaboration retains that type without automatically expanding the
total-complex constructor. Its value is definitionally the same.
The monoidal structure is `SheafOfModules.monoidalCategory` in both presentations;
the zero-map-preservation and complex-total witnesses are proofs. This is a
presentation change by definitional equality, with no change to complexes, maps,
signs, normalization conditions, or target meanings. No consumer requires adaptation.

## Old

```lean
abbrev ordinaryTotal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T)
    (completedIntegralCommRingSheafUnrestricted l E T)
```

## New

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

## Users

`tools/downstream.py Sheaf.Paper.PuritySourceTransports --uses
WeilConjectures.RationalSmoothPurityCanonical.ordinaryTotal` found 118 transitive
importers and only one direct user: the item itself. All listed modules follow.
Other textual hits for the short name belong to different namespaces.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PuritySourceTransports | Q9 | Definitionally identical total tensor; own proof updated. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | M2 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | F7 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | S3 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | G4 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | A3 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | K4 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | S3 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | U4 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | P4 | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No direct ordinaryTotal use; identical data and public interfaces; no adaptation. |

## Status

landed 20261026T070700-L-3642003 2026-10-26 (merge of deliver/Q9/Sheaf.Paper.PuritySourceTransports)
