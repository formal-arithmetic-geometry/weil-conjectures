# AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek

## Reason

The preflight's `leanindex.interface` stores the entire body of an `instance`,
so replacing this instance's `sorry` by a proof is classified as an interface change.
This record documents that conservative classification. No binder, universe, result type,
instance registration, priority, public import, or definition changes. The elaborated
result is Prop, so proof irrelevance makes its particular proof immaterial to consumers.

## Old

```lean
instance isLeftAdjoint_rightDerivedLowerShriek [Finite Λ] :
    (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint :=
  sorry
```

## New

```lean
instance isLeftAdjoint_rightDerivedLowerShriek [Finite Λ] :
    (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint := by
  let c := HasCompactification.compactification f
  let := (Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) c.i)).isLeftAdjoint
  let := isLeftAdjoint_proper_rightDerivedLowerStar Λ c.g
  change (((c.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory ⋙
    ((c.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor).IsLeftAdjoint
  infer_instance
```

## Users

`tools/downstream.py WeilConjectures.SixFunctors.Etale.Derived.UpperShriek --uses isLeftAdjoint_rightDerivedLowerShriek`
reports the item as the only explicit mention outside comments. The table additionally
lists all transitive importers, since they may use the instance implicitly. None requires
adaptation: its type and registration remain exactly the same. Holders are the local
coordination snapshot when this record was written.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedEvaluationPullback | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| TargetsCheck | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | B2 | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Same signature and instances; proof irrelevance; no adaptation. |

## Status

landed 20261013T150349-L-808767 2026-10-13 (merge of deliver/B2/WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)
