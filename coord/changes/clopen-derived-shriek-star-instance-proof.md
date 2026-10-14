# AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar

## Reason

The static interface checker records the whole body of existing instances, so filling this
instance's proof requires a change record even though its signature, visibility and priority
are unchanged. This is solely a proof replacement, plus a proof-only import of
`WeilConjectures.SixFunctors.Etale.LowerShriek.Proper`. No statement or definition changes,
no target meaning changes, and no downstream adaptation is required.

## Old

```lean
instance isIso_derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekToLowerStar A j) :=
  -- Proof sketch: since the range of `j` is clopen, the sheaf-level comparison `j_! ⟶ j_*` is
  -- an isomorphism (both are extension by zero across the complementary open), and `j_*` is
  -- exact. So `Rj_* ≅ D(j_*) ≅ D(j_!)`, compatibly with the comparison.
  sorry
```

## New

```lean
instance isIso_derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekToLowerStar A j) := by
  have : IsIso (openImmersionLowerShriekToLowerStar A j) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
      j.isClosedEmbedding.isClosed_range
  -- Derive the sheaf isomorphism; exactness identifies the derived shriek with D(j_!).
  let e : D((j)_!open[A]) ≅ R((j)_*[A]) :=
    ((j)_!open[A]).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      Functor.rightDerivedFunctorNatIso (asIso (openImmersionLowerShriekToLowerStar A j))
  -- Transfer full faithfulness from extension by zero to the derived pushforward.
  have : D((j)_!open[A]).Full :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).fullyFaithfulLOfIsIsoUnit.full
  have : D((j)_!open[A]).Faithful :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).fullyFaithfulLOfIsIsoUnit.faithful
  have : (R((j)_*[A])).Full := Functor.Full.of_iso e
  have : (R((j)_*[A])).Faithful := Functor.Faithful.of_iso e
  -- The unit of a reflection is invertible on the essential image of its right adjoint.
  have : IsIso (Functor.whiskerLeft D((j)_!open[A])
      (mapDerivedUpperStarLowerStarAdjunction A j).unit) := by
    have : ∀ K, IsIso ((Functor.whiskerLeft D((j)_!open[A])
        (mapDerivedUpperStarLowerStarAdjunction A j).unit).app K) := fun K ↦
      (mapDerivedUpperStarLowerStarAdjunction A j).isIso_unit_app_of_iso (e.app K)
    exact NatIso.isIso_of_isIso_app _
  unfold derivedOpenImmersionLowerShriekToLowerStar
  infer_instance
```

## Users

Source-only `tools/downstream.py WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar` found
272 transitive downstream modules. Its `--uses` search found no explicit mentions
of this instance outside the item itself. The instance proves a proposition, so its changed
proof has no effect on any dependent construction by proof irrelevance. Every signature,
instance registration and public import stays identical. All downstream modules are listed
below with the holder from the local claim snapshot; none is edited.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar | M3 | Original instance proof closed; signature unchanged |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetCoefficientNaturality | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage | K3 | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ClosedCoefficientSourceTransitionIso | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ClosedCoefficientTargetTransitionIso | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.EtaleOpenInjectiveLerayEdge | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RestrictedDerivedEvaluationPullback | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No adaptation; identical proposition and instance API |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No adaptation; identical proposition and instance API |
| TargetsCheck | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Defs | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Properties | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | No adaptation; identical proposition and instance API |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | No adaptation; identical proposition and instance API |

## Status

landed 20261014T185245-L-201837 2026-10-14 (merge of deliver/M3/WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar)
