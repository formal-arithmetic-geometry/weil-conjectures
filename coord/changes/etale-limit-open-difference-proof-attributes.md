# AlgebraicGeometry.Etale.tailOpenDifference_naturality

## Reason

The proof uses local irreducibility annotations to prevent elaboration from expanding
Ext's transported additive group instance, cohomology maps, and inverse-image functors.
The existing theorem's statement, its visibility, the original definitions, and its
public imports stay identical. These attributes are local to this module and do not
propagate to importers. The stage-3 interface detector conservatively flags changed
attribute commands, so this record documents their precise scope. No consumer is adapted.

## Old

```lean
attribute [local irreducible] upperStar openCohomologyRestriction cohomologyMap
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree
```

## New

```lean
attribute [local irreducible] upperStar cohomologyMap Sheaf.H.map
  CategoryTheory.Abelian.Ext.instAddCommGroup
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree
```

After the proved general additive helpers, restriction's existing local annotation is
restored for the theorem:

```lean
attribute [local irreducible] openCohomologyRestriction
```

Only the local elaboration transparency of `Sheaf.H.map` and
`CategoryTheory.Abelian.Ext.instAddCommGroup` is additionally restricted. No constant
or global elaboration attribute is changed; no target's mathematical meaning changes.

## Users

The table lists the module and every module returned by the source-only downstream
inventory. Declaration-name filtering finds just the parent and
`Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform` using the theorem. All
importers continue to see the same signature and definitions; local attributes are
not exported. The theorem retains the same hypotheses and conclusion in every case.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Q2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitAffineSectionDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitFiberDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardGermVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitBinaryComparisonLadder | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitBinaryEventualZero | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitBinaryGeometricLadder | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitBinarySuccessorCoconeSegment | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyBinaryGluing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitOpenDifferenceNaturality | K2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictedCohomologyNeighbourhoodColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.EtaleClassVanishingSpreads | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.GabberCriterion | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.GabberCriterionDegree | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.GabberPrincipalClassLocallyZero | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No exported change; no adaptation. |
| TargetsCheck | unclaimed | No exported change; no adaptation. |
| WeilConjectures | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No exported change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity | unclaimed | No exported change; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No exported change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No exported change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No exported change; no adaptation. |

## Status

landed 20261013T201758-L-3972741 2026-10-13 (merge of deliver/K2/Sheaf.AlgebraicGeometry.EtaleLimitOpenDifferenceNaturality)
