# Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsFactors imports

## Reason

The direct public FactorThru import is redundant. The retained public construction
import already exports it along this all-public path:

`Sheaf.AlgebraicGeometry.EtaleRestrictedTotalConstruction` →
`Sheaf.Paper.EtaleTermwiseHypercohomology` →
`Sheaf.CategoryTheory.HypercohomologyFirstPage` →
`Sheaf.CategoryTheory.CartanEilenbergPresentation` →
`Sheaf.CategoryTheory.DoubleComplexTotal` →
`Mathlib.CategoryTheory.Subobject.Limits` →
`Mathlib.CategoryTheory.Subobject.Lattice` →
`Mathlib.CategoryTheory.Subobject.FactorThru`.

Checked this path in the source files. Every declaration and instance supplied by the
removed edge remains publicly available to every downstream module through that path.
Thus every downstream statement has the same meaning, strength, definitions and imports
available; no target semantics changes or forced adaptations are involved.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleRestrictedTotalConstruction
public import Mathlib.CategoryTheory.Subobject.FactorThru
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleRestrictedTotalConstruction
```

## Users

All 238 downstream modules reported by `tools/downstream.py` are listed below.
Group holders are from the local claim snapshot. Each row is covered by the unchanged
public-export path verified above; no module is adapted. The two direct importers are
`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparison` and
`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | D3 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit | G4 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexAbutmentPresentations | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations | G3 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology | C2 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtalePresentationImageFiltration | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso | B3 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | C3 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | N3 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | N1 | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Same public exports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same public exports; no adaptation. |
| TargetsCheck | unclaimed | Same public exports; no adaptation. |
| WeilConjectures | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same public exports; no adaptation. |

## Status

landed 20261012T223400-L-1635034 2026-10-12 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsFactors)
