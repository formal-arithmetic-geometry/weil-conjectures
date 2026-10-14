# AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek

## Reason

The previous unconditional finite-coefficient instance is false. For Λ = F₂, take
f : ⨿ₙ Pⁿ_C → ⨿ₙ Spec C, which is proper locally on the target. Smooth purity gives
Rf^! Λ on the nth component in degree -2n, so a degree-zero input need not have a
global lower bound after exceptional pullback. The launcher explicitly authorized
correcting this non-target signature and withdrew the old rollback instructions.

A global upper-amplitude bound for Rf_! is sufficient: orthogonality and adjunction
produce the lower bound n-N. This is a bound on the actual left adjoint, not a
repackaged preservation assumption about its right adjoint. We prove the corrected
statement directly. The coefficient-only global instance is corrected likewise.
Both bounded-below classes, their fields, functor constructions and adjunctions
remain exactly the same. Remove the redundant direct public import
WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor: the same module is
publicly re-exported through LowerShriek → UpperLowerStar, so no public API is lost. No statement or definition of Challenge.lean changes;
there is no target semantic change requiring renewed target review.

## Old

```lean
instance hasBoundedBelowUpperShriek (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj := sorry

instance hasBoundedBelowUpperShrieks (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ) where
  hasBoundedBelowUpperShriek _ _ := inferInstance
```

## New

```lean
theorem hasBoundedBelowUpperShriek (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℤ)
    (hN : ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
        DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f

theorem hasBoundedBelowUpperShrieks (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      ∃ N : ℤ, ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
          DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ)
```

These are explicit theorems rather than unconditional instances. The individual
proof gives a lower bound n-N; the global constructor applies it map by map.
Existing generic callers retain their explicit HasBoundedBelowUpperShriek or
HasBoundedBelowUpperShrieks hypotheses. No source caller names either changed
theorem; the direct declaration-bearing importers compile unchanged. The
unclaimed pro-étale UpperShriek module needs its explanatory docstring corrected,
because it had described the retired false instance as automatic. Upper-shriek
composition statements also need explicit mapwise bounded-below hypotheses; their
unclaimed module is adapted in this delivery. Its lower-shriek statements are
kept unchanged by moving the upper-preservation section variables past them.

## Users

The table is the complete transitive source inventory from tools/downstream.py
(the textual named-usage inventory contains only the item itself). Holder values
come from this checkout's coordination snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | X2 | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | S1 | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | S1 | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | N1 | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedEvaluationPullback | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| TargetsCheck | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | The unit-isomorphism theorem now explicitly assumes HasBoundedBelowUpperShriek for i, as its pro-étale Hom equivalence requires. The two lower-shriek fully-faithfulness instances are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Corrected coefficient-only claim in the module docstring; all signatures and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Add explicit HasBoundedBelowUpperShriek hypotheses for f, g and f ≫ g to the three upper-shriek composition declarations; lower-shriek signatures stay unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | No named use of either changed theorem; public definitions and explicit class hypotheses unchanged. |

### Upper-shriek composition adaptation

The original module fails against the corrected dependency with
`failed to synthesize instance Etale.HasBoundedBelowUpperShriek (ModuleCat Λ) f`
at original lines 195, 234 and 310; analogous failures occur for g and f ≫ g.
These are exactly the morphisms whose upper-shriek functors occur in the types.
Add the three mapwise class hypotheses to the upper-shriek declarations only.
The module is unclaimed, so the launcher's unclaimed-module exception authorizes
this necessary signature correction. Moving the upper-preservation hypotheses
hf₂, hg₂, hfg₂ after the lower-shriek statements changes the positional order of
the six preservation arguments to the first upper-shriek theorem; its one caller
in the same module is reordered accordingly. No proof argument is changed.
The Old/New blocks above describe the primary interface change; the exact
composition signature changes are the added mapwise instance binders.

### Closed-immersion pro-étale unit adaptation

This unclaimed module fails at original line 95 with
`failed to synthesize instance Etale.HasBoundedBelowUpperShriek (ModuleCat Λ) i`:
its pro-étale exceptional Hom equivalence takes precisely that étale instance.
Its proof has the same failure at lines 98, 103, 107 and 110. Make the previously
implicit bounded-below prerequisite explicit in that one theorem. The finite-coefficient binder is made explicit at the theorem, with the unused
automatic section binder omitted; its elaborated finite-coefficient prerequisite
is retained. Its two
lower-shriek fully-faithfulness instances do not involve any exceptional functor
and are unchanged. No source module names this theorem, so no further named
caller adaptation is required. The change is to the typing prerequisite, not to
the unit-isomorphism proof.

Old signature:
```lean
theorem isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion
    {Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z Q) :
    IsIso (rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
      (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _))
```

New signature:
```lean
theorem isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion [Finite Λ]
    [Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) i]
    {Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z Q) :
    IsIso (rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
      (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _))
```

## Status

landed 20261014T145820-L-752767 2026-10-14 (merge of deliver/T1/WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)
