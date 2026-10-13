# Algebra.strictHenselization_surjective_quotient_core

## Reason

The old intermediate statement is false for an arbitrary B-action on C/IC. Tag 05WS uses
the induced quotient action. For A=B=C=K=L an algebraically closed field k, I=0 and pi=id,
choose a nonsurjective self-embedding e:k->k as the quotient action. The pointed etale
colimit over k is k with the identity action, whereas this new action cannot be k-algebra
isomorphic to it. For example take k an algebraic closure of Q(t_0,t_1,...) and extend the
shift t_i->t_(i+1) to an embedding of algebraic closures. Its image is algebraic over
Q(t_1,t_2,...) and excludes t_0. This counterexample is mathematical, not Lean-certified.

Repair the intermediate core to return the quotient action it constructs. This is the
source's quotient conclusion and preserves the already-existential caller exactly.
No target statement or existing definition changes, and no target interpretation changes.

## Old

```lean
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))] :
    IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

## New

```lean
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (_hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

## Users

The textual downstream scan finds only the core itself and
Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient as declaration users. The latter
is unclaimed in the local claim records. Its entire signature and visibility stay
identical. Its final application must obtain the action qB' and the proof hq from the
new core, then package those in the same existential conclusion; these are the only
changed proof lines. The original use expected a proof for qB, and now receives an
existential pair, so it necessarily fails against the changed core. All transitive
importers are inventoried below; they see the same surjective_quotient statement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient | unclaimed | Forced proof adaptation: consume the constructed quotient action; signature identical. |
| TargetsCheck | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Interface and mathematical statement unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Interface and mathematical statement unchanged; no adaptation. |

## Status

landed 20261013T215603-L-897456 2026-10-13 (merge of deliver/F1/Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore)
