# finiteProperBaseChange_of_coefficientIso

## Reason

The residue proof needs the finite proper formulas for continuous finite coefficients, not
only their sheafified-constant specialization. The existing private helper already proves
exactly this. Export that theorem and state its projection clause with the existing canonical
`moduleObjectProjectionMap`. Unfold its data record in the existing projection proof.
Unfold the same record when the public finite theorem uses the helper; its statement
is unchanged. This makes the actual projection API usable without expanding it in consumers. Publicly import its
encoding dependency, while retaining the original `import all` for private proof helpers.
No existing public statement or definition changes, and no target meaning changes.

## Old

```lean
private theorem finiteProperBaseChange_of_coefficientIso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar Λ p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((finiteProperExchange Λ
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso ((((derivedUpperStarLowerStarAdjunction Λ p.left).rightAdjointProjectionMap
        (leftDerivedUpperStarTensor Λ p.left)).app K.obj).app M.obj))
```

## New

```lean
theorem finiteProperBaseChange_of_coefficientIso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar Λ p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((finiteProperExchange Λ
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso (moduleObjectProjectionMap Λ p.left K.obj M.obj))
```

The original private encoding import stays. Add public imports of
`Sheaf.Paper.FiniteDiscreteOrdinaryEncoding` and
`Sheaf.Paper.ModuleObjectProjectionMap` for the exported signature.

## Users

`tools/downstream.py Sheaf.Paper.FiniteProperBaseChange --uses
finiteProperBaseChange_of_coefficientIso` found only its own module mentioning the
previously private name. All transitive consumers are listed below; none needs adaptation.
Claims were read on 2026-10-25; the adapted finite module was rechecked unclaimed on 2026-10-26. The source-library boundary is preserved: no source-root
module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficients | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficientsData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarCochainNormalization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarRealizationData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | E1 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | H2 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | U5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | A4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | W6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Y6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | F9 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | G6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | E5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | K4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | F3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | J1 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | H4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | K9 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | M7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | J6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | C3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | K7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | D3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | G1 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | J9 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | D3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | K6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | P2 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | S6 | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | D9 | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Export its proved helper with the canonical projection map; unfold its data at both uses. |
| Sheaf.Paper.IntegralResidueProperFormulas | P6 | Apply the helper to continuous residue coefficients. |

## Status

landed 20261026T023730-L-597739 2026-10-26 (merge of deliver/P6/Sheaf.Paper.IntegralResidueProperFormulas)
