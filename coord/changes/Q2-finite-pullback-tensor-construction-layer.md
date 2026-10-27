# WeilConjectures.canonicalFinitePullbackTensor

## Reason

Separate the existing constructions from the coherence theorems so that a new theorem on
flat K-flat representative inputs can be imported by the coherence proof without an import
cycle. All moved public declarations retain their original signatures, names, attributes
and bodies. The sole renamed construction body is exposed under
`finitePullbackTensorConstruction`; the existing `canonicalFinitePullbackTensor` becomes
its definitionally identical API wrapper. This is one construction with an alias.

The original module publicly imports both construction layers; their transitive public
imports include the same modules the original imported publicly. Its existing public names remain visible.
No target statement or mathematical definition changes. The new natural isomorphism
packages the same five comparison factors, so its components agree definitionally with
the old comparison family. No selected object is added from an existence-only theorem.

## Old

Original module: `Sheaf.Paper.FinitePullbackTensorComparison`.

```lean
def canonicalFinitePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@FinitePullbackTensorComparison l _ E _ _ _ X Y f n hX hY) := by
  letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  exact fun M N ↦
    ((Functor.mapDerivedCategoryNatIso
      (pullbackTensorFiniteRealization l E f n)).app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N))).symm ≪≫
    (proEtaleRingDerivedPullback f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).mapIso
        ((pullbackTensorFiniteModelIso l E Y n).app (M,N)).symm ≪≫
    (proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)).app (M, N) ≪≫
    (pullbackTensorFiniteModelIso l E X n).app
      ((proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj M,
      (proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj N) ≪≫
    (finiteIntrinsicDerivedTensor l E X n).mapIso
      (Iso.prod ((Functor.mapDerivedCategoryNatIso
        (pullbackTensorFiniteRealization l E f n)).app M)
        ((Functor.mapDerivedCategoryNatIso
          (pullbackTensorFiniteRealization l E f n)).app N))

-- Keep the constructed comparison sealed while elaborating its coherence equations.
```

## New

The unchanged construction body lives at
`lean/Sheaf/Paper/FinitePullbackTensorConstruction.lean`, under
`WeilConjectures.finitePullbackTensorConstruction`. The original public definition is:

```lean
def canonicalFinitePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@FinitePullbackTensorComparison l _ E _ _ _ X Y f n hX hY) :=
  finitePullbackTensorConstruction l E f n

-- Keep the constructed comparison sealed while elaborating its coherence equations.
```

The original module publicly imports `Sheaf.Paper.FinitePullbackTensorConstruction`
and `Sheaf.Paper.FinitePullbackTensorBraiding`. The first layer contains the four
comparison-family types, coefficient and site instances, and finite restriction and
realization definitions. The second contains the signed total and derived braiding
constructions and proved uniqueness theorems previously in the item. These
retain their signatures and bodies verbatim. The added
`finitePullbackTensorConstructionIso` composes the same natural isomorphisms instead of
taking their components first; it does not assert any new coherence property.

## Users

`tools/downstream.py Sheaf.Paper.FinitePullbackTensorComparison` lists the following
transitive consumers. The read-only snapshot does not record a module claim for these
paths; none is edited. The only direct importer is compiled against this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.AllStageCtfPullbackUnit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.AmbientComparisonSystemExistence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.AugmentedIntegralDescent | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.AutomorphismSquareRationalScalar | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ClopenCommonCompactSupport | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ClopenIntegralRestriction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ClopenRoosIntegralDescent | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CoefficientDualModelTransport | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CoherentRationalPullbackIdentity | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageEvaluationNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStagePullbackIdentity | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageShiftedUnitTensor | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageTensorBraidingNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageTensorLineCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageTensorLineCoherenceNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageTensorRightUnitorNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageWeilIterate | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonStageWeilLinearDual | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CommonTensorBraidingNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedComparisonCanonicalIdentification | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedComparisonQuotientNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedComparisonQuotientRealization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedConstantRightUnit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedInverseImageScalarCounit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedPullbackTensorComparison | not recorded locally | Direct importer; compile unchanged against extraction |
| Sheaf.Paper.CompletedUnitAdmissible | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitMultiplicationComponents | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitPullbackData | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitPullbackTower | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitReduction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitScalarNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.CompletedUnitStrictComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstantGeometricStalkUnit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstantTwistCoefficientComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstantWeilStageCompatibility | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstantWeilStructure | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstructiblePullbackTExact | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ConstructibleTruncations | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DerivedPullbackTensorIso | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DlLocalHeartAbelianEvaluation | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DlLocalHeartCoverBasisZero | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DlLocalHeartCoverDefects | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdCoefficientComparisonSystem | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdCommonStageComparisonDescent | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdCompletionFiniteStageLinear | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdIntegralScalarDescentInputs | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdScalarPullbackRealizationIdentification | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteCompositorCounit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProductEvaluationSwap | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProductNormalForm | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProperCompositorMate | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProperProductMaps | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProperProductTranspose | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteProperTransportTranspose | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteRestrictionConstructibleVertices | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteRestrictionDiagramModels | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FiniteRestrictionStrictTransport | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FourierTraceFunctions | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FourierTrivialCharacterUnit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FrobeniusFixedPairComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonCanonicalShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonCompositionReduction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonPullbackRealizationShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonScalarRealizationShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralComparisonSystemData | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralCompositionCounitImages | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralPointTransportTowerRealization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralPullbackComparisonRealization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralPullbackReductionCounit | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralPullbackResolutionMatching | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralReductionClopenComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralReductionFiniteClopenBounds | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralScalarPullbackCompletionNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IntegralScalarPullbackCounitCompatibility | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismDerivedPullback | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismFieldTransport | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismFieldTransportClauses | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismFieldTransportCommonStage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismFieldTransportFiniteStage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismFieldTransportRationalScalar | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismPullbackRawStage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IteratedReturnTransportData | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.IteratedReturnTransportScalarCalculus | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.LocalFrobeniusTrace | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.LocalWeilModelTraceIndependence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedCommonEvaluationForStructure | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedCommonEvaluationNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedIntegralGeometricCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedIntegralMixedCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedIntegralScalarCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.OrdinaryDerivedProductLegTransposes | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PbcConstantWeilTwist | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PbcWeilCoefficientComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionReindexCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionReindexModels | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionReindexShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionReindexSubstitution | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionTensorModels | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCompletionTensorNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodCounitScalarWordCoordinates | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodNormalizedTensorSignedShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingCompletionNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingCompletionUnitTensor | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingDerivedComparisons | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingGoodComplex | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingRestrictedTower | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingRoosShiftCompatibility | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingSignedRoosShift | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingStrictComparisons | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingTensorCoefficientTransition | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingTensorConstruction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingTensorFamilyCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingTensorSignedShifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PodReindexingTensorSubstitution | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointAutomorphismDerivedTransportInverse | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointEquivariantCommonStage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointEquivariantDiagramData | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointEquivariantDiagramLift | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointEquivariantFiniteScalar | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointEquivariantOriginalDiagram | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointExactDerivedModel | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartExactness | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartFiniteStage | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartFiniteStageData | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartFiniteStageEquivalences | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartFiniteStageScalars | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointHeartFiniteStageTruncations | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointInverseImageCoefficientTower | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointRealizationStandardCohomology | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointScalarCompatibleTransportTransfer | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointScalarSingleStepCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PointWeilFiniteStageDescent | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ProperFiniteNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RationalCoefficientCategoryComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RationalPullbackFibreComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RationalRestrictionComparisonCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RationalScalarSingleStepNormalization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RealizedPullbackComparisons | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.RegularCoefficientCoherentReduction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ReturnScalarSquares | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.ScalarExtensionTowerCoherence | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.SemilinearFieldOperationLifts | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.SfFrameworkThetaShiftCompatibility | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.SimultaneousIntegralPullbackComparisons | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.WeilComplexTraceFunction | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransport | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransportQbarNaturalTransformation | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.SixFunctors.FrobeniusPointTransportRationalScalar | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.TraceFormula.PointExactRealization | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.TraceFormula.PointTransportComposition | not recorded locally | Same names, signatures, data and public reexports; no adaptation |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | not recorded locally | Same names, signatures, data and public reexports; no adaptation |

## Status

landed 20261026T130643-L-3488572 2026-10-26 (merge of deliver/Q2/Sheaf.Paper.FinitePullbackTensorComparison)
