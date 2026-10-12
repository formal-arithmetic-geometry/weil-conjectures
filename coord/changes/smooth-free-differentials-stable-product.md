# Algebra.smooth_free_differentials_strictly_standard_power

## Reason

The original Lean hypothesis parses as
`Nonempty (KaehlerDifferential R B × ((Fin s →₀ B) ≃ₗ[B] (Fin t →₀ B)))`.
It imposes no freeness condition on the differentials. In particular `s=t=0` supplies
this hypothesis for every algebra, by pairing the zero differential with the identity
of the zero free module. The scratch proof StableParseCheck.lean compiles this witness
and projects the equivalence from the second component, confirming the elaborated type.

Stacks Tag 07EZ(e) and the unchanged mathematical DAG statement require
`Nonempty ((KaehlerDifferential R B × (Fin s →₀ B)) ≃ₗ[B] (Fin t →₀ B))`.
Parenthesizing the product repairs the formalization; no binder, universe, conclusion,
or definition changes. This is the source's stable-freeness hypothesis, not an auxiliary
hypothesis introduced to help the proof. A smooth algebra with different ranks of
its differentials on different components (e.g. `k × k[X]`) illustrates why the original
hypothesis is insufficient: at `a=1` it holds, whereas the necessary stable-freeness
condition for strict standardness does not.

## Old

```lean
theorem smooth_free_differentials_strictly_standard_power
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    [Algebra.Smooth R (Localization.Away a)]
    (s t : ℕ)
    (hstable : Nonempty
      (KaehlerDifferential R (Localization.Away a) × (Fin s →₀ Localization.Away a)
        ≃ₗ[Localization.Away a] (Fin t →₀ Localization.Away a))) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (a ^ e)
```

## New

```lean
theorem smooth_free_differentials_strictly_standard_power
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    [Algebra.Smooth R (Localization.Away a)]
    (s t : ℕ)
    (hstable : Nonempty
      ((KaehlerDifferential R (Localization.Away a) × (Fin s →₀ Localization.Away a))
        ≃ₗ[Localization.Away a] (Fin t →₀ Localization.Away a))) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (a ^ e)
```

## Users

`tools/downstream.py Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
--uses Algebra.smooth_free_differentials_strictly_standard_power` lists 193 import
descendants and no occurrence of the declaration outside its own module. Whole-library
`rg` for the short name confirms this. The two direct importers currently have sorry
proofs and do not apply the theorem. They need no adaptation; their types and proofs
are unchanged. No target statement uses this theorem as data or mentions its signature,
and no definition has changed, so target meanings remain unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower | Y2 | Restore the intended product-equivalence hypothesis; prove the corrected theorem by a decomposition. |
| Sheaf.RingTheory.PopescuSeparablePreparationCore | unclaimed in the local claim snapshot | Import only; no call or type mentioning this declaration. |
| Sheaf.RingTheory.PopescuCharPPreparationGlobal | unclaimed in the local claim snapshot | Import only; no call or type mentioning this declaration. |

All transitive import descendants from the read-only local snapshot are listed below.
Each was checked by the textual declaration-use scan; none uses this declaration.
Holder information is only the local claim snapshot, not a fresh server claim.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparationCore | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparationGlobal | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuSeparablePreparation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuSeparablePreparationCore | S3 | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| TargetsCheck | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | Import descendant only; no occurrence of the declaration; statement unchanged. |

No adapted modules are delivered. The mathematical statement in the existing node was
already correct; only its `lean.statement` record is corrected, so there is no
`statement_change` to the mathematical node.

## Status

landed 20261012T184401-L-4025999 2026-10-12 (merge of deliver/Y2/Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower)
