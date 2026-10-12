# baseChange_sigmaScheme_iso (redundant public import)

## Reason

Mathlib.AlgebraicGeometry.Limits already publicly imports
Mathlib.AlgebraicGeometry.Pullbacks. The direct second import is redundant;
removing it preserves all exported declarations and instances. The theorem
signature and proof are unchanged by this cleanup and compile successfully.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Limits
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteStalkTests | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGeometricPointSectionsStalkNatural | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafUnique | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteSourceLisse | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.GmPicardPullback | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseStrata | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantCounit | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| TargetsCheck | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Defs | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Properties | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not consulted (no adaptation) | No effect: identical public import closure through Limits; no adaptation. |

No definition or target meaning changes; no target review needs reopening.

## Status

landed 20261012T130503-L-1300066 2026-10-12 (merge of deliver/P2/Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange)
