# WeilConjectures.IntegralOrdinary.tensorModel and TensorAugmentationNormalized

## Reason

Move the two existing tensor-model declarations to the new one-scheme tensor reduction
module, so the lower normalization claims can use them without importing the theorem
that they prove. The item publicly imports that module. The old names, types, bodies,
visibility, reducibility attribute, universes and hypotheses are preserved. The item's
original tensor/pullback augmentation statement is unchanged. This is an extraction,
not a change to the mathematical definitions.

## Old

Declared in lean/Sheaf/Paper/IntegralTensorPullbackAugmentation.lean:

```lean
@[reducible] def tensorModel (X : Scheme.{u}) :
    ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X) where
  tensor := ConstructibleTensorModel.ordinaryTensor l E X
  representative := by
    let i : (proEtaleFlatRepresentatives X
        ((PurCompactSupport.completed l E).ring X)).FullSubcategory ⥤
        (integralOperationsGoodComplex l E X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun P hP ↦
        ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1, hP.2⟩)
    with_unfolding_all
      exact Functor.isoWhiskerLeft (i.prod i)
        (ConstructibleTensorModel.tensorRepresentativeIso l E X)

/-- The forward tensor augmentation is fixed on entire flat-term K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 0941
(blueprint: lem-sf-integral-tensor-pullback-augmentation). -/
def TensorAugmentationNormalized (X : Scheme.{u})
    (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
    (ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q) ≫
        τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map
        ((ConstructibleTensorModel.tensorCompletionChain l E X).app (P.obj, Q.obj))
```

## New

Declared in lean/Sheaf/Paper/IntegralTensorReductionAugmentation.lean and publicly
re-exported from the old module:

```lean
@[reducible] def tensorModel (X : Scheme.{u}) :
    ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X) where
  tensor := ConstructibleTensorModel.ordinaryTensor l E X
  representative := by
    let i : (proEtaleFlatRepresentatives X
        ((PurCompactSupport.completed l E).ring X)).FullSubcategory ⥤
        (integralOperationsGoodComplex l E X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun P hP ↦
        ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1, hP.2⟩)
    with_unfolding_all
      exact Functor.isoWhiskerLeft (i.prod i)
        (ConstructibleTensorModel.tensorRepresentativeIso l E X)

/-- The forward tensor augmentation is fixed on entire flat-term K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 0941
(blueprint: lem-sf-tensor-reduction-augmentation). -/
def TensorAugmentationNormalized (X : Scheme.{u})
    (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
    (ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q) ≫
        τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map
        ((ConstructibleTensorModel.tensorCompletionChain l E X).app (P.obj, Q.obj))
```

The item replaces its direct public ConstructibleTensorCompletionChain import with
IntegralTensorReductionAugmentation, which publicly re-exports that same chain module.
Its other public imports are retained. IntegralReductionTensorPullback is a proof import.
No existing source-library declaration or module is changed.

## Users

The table includes the full source downstream inventory. Textual hits for tensorModel
in AdicTraceTransposeData and AdicTraceTransposeCoefficientCalculus refer to their own
AdicTraceTranspose.tensorModel abbreviation; the only external direct consumer of the extracted
IntegralOrdinary declarations is IntegralOrdinaryTensorPullbackNormalization.
No consumer needs a source adaptation, since the original module re-exports both names.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization | unclaimed | Direct caller; compile its unchanged source against the delivery. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralProjectionOperationPresentation | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralProperOperationProjection | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionReduction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Publicly re-exported declarations retain their names, signatures and bodies; no adaptation. |

## Status

landed 20261027T180554-L-3877743 2026-10-27 (merge of deliver/F1/Sheaf.Paper.IntegralTensorPullbackAugmentation)
