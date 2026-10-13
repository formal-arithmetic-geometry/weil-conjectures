# Algebra.exists_popescu_reduction_presentation_of_factor

## Reason

The original statement omitted finite presentation of A over R, which Tag 07CK assumes. For R = Lambda = C = Z, I = 0 and A the polynomial ring in infinitely many variables, augmentation satisfies the hypotheses, but any finite list of relations leaves infinitely many free variables in the nonzero displayed quotient, contradicting standard smoothness and finite generation. Add [FinitePresentation R A], as in the source and the sole caller.

The source is https://stacks.math.columbia.edu/tag/07CK, with the permanence lemma https://stacks.math.columbia.edu/tag/00F4. This is an intermediate theorem correction authorized by stage 3, not a change to a target or a definition. No dependent declaration changes meaning.

## Old

```lean
theorem exists_popescu_reduction_presentation_of_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] Λ)
    (C : Type (max u v w)) [CommRing C] [Algebra (R ⧸ I) C]
    (hC : IsStandardSmooth (R ⧸ I) C)
    (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
    (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ))
    (hfactor : δ.comp β = reducedAlgHom R Λ I A φ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈
        I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i)))
```

## New

```lean
theorem exists_popescu_reduction_presentation_of_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ)
    (C : Type (max u v w)) [CommRing C] [Algebra (R ⧸ I) C]
    (hC : IsStandardSmooth (R ⧸ I) C)
    (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
    (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ))
    (hfactor : δ.comp β = reducedAlgHom R Λ I A φ) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈
        I.map (algebraMap R Λ)) ∧
      IsStandardSmooth (R ⧸ I)
        (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
          Ideal.span (Set.range fun i ↦
            MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i)))
```

## Users

The source-only downstream scan has 202 modules. Exact declaration-name search finds only the assigned module and the caller `Sheaf.RingTheory.PopescuReductionPresentation`. The caller has `[FinitePresentation R A]` already and was compiled unchanged against the corrected module. No module is adapted. Holder information is from the local snapshot, which contains no active JSON claim records for these modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.PopescuLiftNilpotent | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuLiftOnce | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuLiftOnceCore | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuLiftTwice | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalResolution | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuReductionPresentation | unclaimed in local snapshot | Existing instance supplies the new hypothesis; unchanged source compiled against the correction. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.PopescuStandardReductionFactor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| TargetsCheck | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | No direct use of the changed declaration; signatures and definitions unchanged. |

## Status

landed 20261013T024055-L-3341242 2026-10-13 (merge of deliver/Y3/Sheaf.RingTheory.PopescuReductionPresentationFromFactor)
