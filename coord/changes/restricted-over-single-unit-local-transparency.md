# restrictedOverSingle_unit local proof transparency

## Reason

The proof uses existing inverse-image coherence without unfolding the inverse-image
functors. The static delivery checker treats every changed command, including a
local attribute, as an interface change and requires this record. This record
covers that conservative classification; no definition or statement has changed.
There is no forced adaptation and no target semantics review is reopened.

## Old

No local irreducibility attribute in this module. The signature of
AlgebraicGeometry.Etale.restrictedOverSingle_unit is unchanged.

## New

```lean
attribute [local irreducible] upperStar upperStarComp upperStarId
```

This is a local elaboration setting scoped to this module. It neither modifies
the definitions nor exports an attribute to importers. Eight proved private
helpers and the complete proof of restrictedOverSingle_unit were added.

## Users

The complete downstream import closure reported by tools/downstream.py is listed
below, together with the item itself. No module is adapted: every existing
statement and definition has exactly its previous meaning and signature.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapInjective | R1 | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapIsIso | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapNaturality | W3 | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapSurjective | Q3 | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNegative | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RestrictedOverAbelianComplexData | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| TargetsCheck | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged signature and definitions; local attribute is not exported. |
| Sheaf.AlgebraicGeometry.RestrictedOverSingleUnit | X3 | Unchanged signature and definitions; local attribute is not exported. |

## Status

landed 20261013T161732-L-1461406 2026-10-13 (merge of deliver/X3/Sheaf.AlgebraicGeometry.RestrictedOverSingleUnit)
