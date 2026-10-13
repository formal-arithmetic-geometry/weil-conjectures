# Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology import visibility

## Reason

The local first-page representative calculation does not use stationary pages. Its
statement needs the CE sections total and normalized positive pages. Removing the
unused stationary-page public import prunes its proof closure. The theorem signature,
definitions and statement meaning are unchanged; no target semantic review reopens.
This is an import-visibility change only, required to prune unused imports.

## Old

```lean
public import Sheaf.Paper.EtaleCEStationaryPageNaturality
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
```

## New

```lean
public import Sheaf.Paper.EtaleCETotalSections
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.Paper.EtaleCENormalizedRowRepresentatives
```

## Users

The sole direct importer is Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages. It
already publicly imports EtaleCEStationaryPageNaturality itself. Its original source
compiled unchanged against the sandbox overlay (48.5 seconds including compilation
slot wait). Therefore no adaptation is forced or delivered. Every further consumer
still receives the former stationary declarations through this importer. This preserves
the downstream declarations and their meaning. The full transitive downstream list
from tools/downstream.py is recorded below, with holders from the available local
claim snapshot. The maintainer verifies the full library after landing.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology | M4 | Proof and imports changed; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit | C3 | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexAbutmentPresentations | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexUniformPages | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleHypercohomologyUniformBound | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | Y3 | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.EtaleCECoherentPrescribedResolutions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages | unclaimed | Original compiled unchanged; publicly reexports the stationary module. |
| Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.EtaleCESupportedFirstPageLifts | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.EtaleHypercohomologySupportedCETotals | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.EtaleHypercohomologySupportedResolutionMaps | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| TargetsCheck | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No source edit; receives stationary declarations through the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No source edit; receives stationary declarations through the direct importer. |

## Status

landed 20261013T134102-L-72090 2026-10-13 (merge of deliver/M4/Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology)
