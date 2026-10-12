# CategoryTheory.injective_module_cech_cohomology_isZero

## Reason

Repair reviewer X-38a84 point 4: the old signature is false, certified by
Triangle.false_signature in the report. Restrict ring, abelian, module and index
universes to the hom universe v, exactly as requested. The revised theorem is
proved from existing common-universe declarations. Five etale callers need forced
proof adaptations since their hom universe is u but coefficients and indices are
u+1. Their declarations and all Challenge targets keep their signatures and
visibility. A separate max-universe presheaf cocycle-lifting step, strictly below
sheaf acyclicity, is left as a named theorem with its source and full proof plan.
No definition changes, and no arbitrary data is selected from an unproved theorem.

## Old

```lean
theorem injective_module_cech_cohomology_isZero
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{r})
    [HasSheafify J.toGrothendieck AddCommGrpCat.{s}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{s}]
    (I : SheafOfModules.{s} R) [Injective I]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((S.cohomologyFunctor p).obj I.val.presheaf)
```

## New

```lean
theorem injective_module_cech_cohomology_isZero
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{v})
    [HasSheafify J.toGrothendieck AddCommGrpCat.{v}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (I : SheafOfModules.{v} R) [Injective I]
    {T : Type v} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((S.cohomologyFunctor p).obj I.val.presheaf)
```

## Users

The downstream.py --uses search finds the changed module and five direct callers.
The following table also includes all 303 transitive importers. Claim holders
are read from the current claim files; all five forced adaptations are unclaimed.
Only their failed invocation blocks and proof-only imports change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | T1 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit | F3 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleHigherDirectImageCyclicReduction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitAffineSectionDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitFiberDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardGermVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleBaseChangeRestrictScalars | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineCorrectedLift | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineDegreeZeroKernel | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineEventualZero | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyAffineComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyBinaryGluing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyDegreeZeroDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic | unclaimed | Forced proof/import adaptation; every existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictedCohomologyNeighbourhoodColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | J2 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | R1 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1 | unclaimed | Forced proof/import adaptation; every existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic | unclaimed | Forced proof/import adaptation; every existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1 | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology | unclaimed | Forced proof/import adaptation; every existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison | unclaimed | Forced proof/import adaptation; every existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.PrimeInjectiveCohomologyComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.PullbackIsoTorsionColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit | H2 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | B2 | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic | V2 | Correct common-universe signature and close its proof from existing declarations. |
| Sheaf.Paper.EtaleClassVanishingSpreads | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.Paper.GabberCriterion | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.Paper.GabberCriterionDegree | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.Paper.GabberPrincipalClassLocallyZero | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer; no declaration use, public interface change or source adaptation. |

## Status

landed 20261012T202256-L-710012 2026-10-12 (merge of deliver/V2/Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic)
