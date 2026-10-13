# AlgebraicGeometry.Etale.higherDirectImageRawOverPullback

## Reason

Repeated single-file compiles of the original expanded definition plus even the
restriction specialization exceeded the launcher's 60-second limit. The unchanged
module compiled in 45 seconds. Factor the definition through the existing
higherDirectImageRawTrianglePullback with exactly the displayed coefficient morphism.
Unfolding that construction gives the previous expression, with the equality proof
identified by proof irrelevance. No data or mathematical statement changes.
The new body requires the triangle module as a public import. No target signature changes.
The meaning of targets using this definition is preserved by definitional equality.
As required by stage 3 section 3, the semantic review of any target using this definition
is reopened for the reviewer to verify that identical expansion.

## Old

```lean
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])).hom.app _) ≫
    (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((f.left)^*[ModuleCat.{u + 1} Λ]).map z ≫
    (D+((f.left)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
    (shiftFunctor _ q).map
      ((((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

## New

```lean
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  higherDirectImageRawTrianglePullback Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) q _ _
    ((((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G)) U z
```

## Users

`tools/downstream.py` finds 202 transitive downstream modules and seven textual
users (including the item). All have unchanged statements: the new definition
has the same type and is definitionally equal to the old expression. The six
external direct users use the named pullback and its existing theorems; none
unfolds its implementation. No module outside the held item is adapted.
For untouched modules the holder column says `not adapted` when no local claim
record is available; no adaptation depends on a claim exception.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | V1 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | C2 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | V1 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackComposition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula | U2 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity | M4 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | N1 | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| TargetsCheck | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Defs | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Inversion | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Perverse | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Properties | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | Definitionally identical expansion; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | Definitionally identical expansion; no statement change or adaptation. |

## Status

landed 20261013T100155-L-2495270 2026-10-13 (merge of deliver/V1/Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality)
