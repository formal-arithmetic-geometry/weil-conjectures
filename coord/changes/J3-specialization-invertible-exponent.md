# AlgebraicGeometry.Etale.FiniteSmoothPurity.specialization_normalExchange

## Reason

The finite-coefficient DNC theorem assumes its annihilator N invertible on the base. The previous strict-factor signature omitted that source assumption, whereas its sole caller already has hS. Uniqueness of normalized Rees-family trivializations and the dualizing-line calculation require it. Restore this assumption explicitly; do not count this as proving the old all-characteristics statement. No target statement, shared definition, instance, attribute or public import is changed.

## Old

```lean
theorem specialization_normalExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    [IsSeparated g'] [QuasiCompact g'] [HasCompactification g']
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection)
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family A g' s' ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).obj
        (sectionInvariant A g' s'))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized A g' s' hs' κ') :
    (ordinaryFinitePullback A b).map
        (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        NoetherianSectionSpecialization.specialization A g' s' κ'
```

## New

```lean
theorem specialization_normalExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    [IsSeparated g'] [QuasiCompact g'] [HasCompactification g']
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection)
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family A g' s' ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).obj
        (sectionInvariant A g' s'))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized A g' s' hs' κ') :
    (ordinaryFinitePullback A b).map
        (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        NoetherianSectionSpecialization.specialization A g' s' κ'
```

## Users

The downstream command reports 166 downstream modules and two textual users (the declaration and its caller). All are listed; only the existing caller is adapted. The caller is unclaimed in the current server claim records. Other rows are unchanged, regardless of concurrent ownership.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.CompositeProjectionCoefficients | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.CompositionComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.CondensedIntegralEndpoints | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteProCoefficientCounitTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedSpecialization | unclaimed | One proof call now supplies its existing hS; public statements unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothNormalizedExistence | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothOrientationBaseChange | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothProQuotientTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSmoothZeroOrientationCoordinates | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerCore | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerProperties | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerZero | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.OrientationScalarPropagation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.QuotientInverseOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TateTensorNormalizedSquare | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TateTensorQuotientBalancing | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerFactorOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerFactorTensor | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerGeometricPurityAssembly | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerGeometricPurityData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerIsomorphismPullback | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerMuEvaluation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerPurityPresentationRetagging | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerSemilinearPurityFactors | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTateSplitNormalized | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTensorPresentationRetagging | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportCondensedStageRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralChartRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralCompositionRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralCounitData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.TransportIntegralStageConstruction | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| TargetsCheck | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed / unchanged | No direct occurrence; imports continue through the parent, whose public statement is unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange | J3 | Assigned item: restores source invertibility hypothesis; proof reduced to automorphism lemma. |

## Status

landed 20261027T234017-L-4161416 2026-10-27 (merge of deliver/J3/Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange)
