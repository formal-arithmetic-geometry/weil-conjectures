# AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_epi

## Reason

Repair reviewer E2. The original universal compatibility claim is false: the pointed diagonal F → F × F is not epic. The corrected claim explicitly requires that i itself exhibit a localization. This is an intermediate theorem, not a Challenge target. No definitions or target signatures change. The sole caller cannot discharge the new hypothesis from its compatibility lemma, so its unchanged existence statement is restored as a named descent obligation instead of retaining a false proof. Its natural-language proof is completed. The forced lines are its former proof body (old lines 38–44), replaced by `sorry`; the now unused proof imports are removed.

## Old

```lean
theorem etaleResidueTriples_primeLocalization_component_extension_epi
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (hα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (hφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ) : Epi i
```

## New

```lean
theorem etaleResidueTriples_primeLocalization_component_extension_epi
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (_hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (_hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (_hα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (_hφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ)
    (M : Submonoid c.B)
    (hlocal : letI := i.hom.toAlgebra; IsLocalization M t.B) : Epi i
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxEpi | G3 | Corrected localization hypothesis; proved without sorry. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselizationCore | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeEquiv | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeExtension | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComparison | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtension | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUnique | unclaimed | No signature or definition changes; no adaptation required. |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAux | unclaimed | Forced proof repair; exact signature and visibility preserved; descent sorry restored. |
| TargetsCheck | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature or definition changes; no adaptation required. |

## Status

landed 20261014T004102-L-2834063 2026-10-14 (merge of deliver/G3/Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxEpi)
