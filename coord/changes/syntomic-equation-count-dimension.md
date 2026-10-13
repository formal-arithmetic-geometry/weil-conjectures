# Algebra.equationCount_comparison_dimension

## Reason

The old universal statement is false. Over any field k, set n=c=1 and f=0,
T=k[x]/(0)=k[x], S=T, π=id, u=1 and take any prime q. Surjectivity, the
localization bijection, u outside q and c≤n all hold. The base fibre is an
affine line and has local topological dimension 1 at every point; the old
conclusion gives 0. Equivalently, a zero equation changes the count but not the
ideal. STATEMENT-DISPUTED applies to the old signature, which this change repairs.

Stacks 00SC sets c to the height difference, not the cardinality of an arbitrary
family. In 00SY the elements are selected as a conormal residue-space basis of
that size. The old split discarded this equality from its core's output and
incorrectly recovered it from a localization isomorphism. Add the known dimension
of the S fibre as the dimension-transport premise. It is supplied by a new,
strictly lower kernel-generator-selection theorem in the caller. The proof of
transport itself is complete, using no Sheaf proof dependencies.

Source read: https://stacks.math.columbia.edu/tag/00SY,
https://stacks.math.columbia.edu/tag/00SC,
https://stacks.math.columbia.edu/tag/00P2.
The recorded local source path is unavailable on this machine; the primary
Stacks pages were read directly. No target statement or used definition changes.

## Old

```lean
theorem equationCount_comparison_dimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
    (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] S)
    (u : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
    (hsurj : Function.Surjective π) (hu : π u ∉ q.asIdeal)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u))
    (hle : c ≤ n) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        ((q.comap π.toRingHom).comap
          (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))))
        ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ)
```

## New

```lean
theorem equationCount_comparison_dimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
    (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] S)
    (u : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
    (hsurj : Function.Surjective π) (hu : π u ∉ q.asIdeal)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u))
    (hdim : topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) =
        (n - c : ℕ)) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        ((q.comap π.toRingHom).comap
          (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))))
        ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ)
```

## Import repair in the second reading

Removed the unused public Mathlib.RingTheory.RingHom.Flat import from
SyntomicEquationCountComparisonDimension. The file compiles without it.
Its sole direct importer SyntomicEquationCountComparison has its own public
Flat import, preserving that caller's exports to all transitive users.
The new selection module's three planned proof dependencies are private imports.
No signature or definition changes in this import repair.

## Users

`tools/downstream.py ... --uses Algebra.equationCount_comparison_dimension`
found 207 transitive importers and one external direct declaration user. All
other importers see the unchanged public signature of that caller; no definitions
changed, so the target meanings remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.SyntomicEquationCountComparisonDimension | F1 | Correct and prove its intermediate statement. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuDesingularizeLiftingApply | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLiftOne | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLiftSmooth | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLiftSmoothSpecial | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLiftSolution | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLifting | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuLiftingWitness | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuSmoothLiftModuloEight | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuSmoothLiftModuloEightAux | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| Sheaf.RingTheory.SyntomicEquationCountComparison | unclaimed | Forced proof and docstring adaptation; signature and visibility unchanged. |
| TargetsCheck | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No edit; target statements and definitions unchanged through the unchanged caller interface. |

The adapted caller uses proof-only `import all` for Core and adds the new
SyntomicCodimensionLocalKernelGenerators import, reuses the private
exists_multiplier_of_localized_le helper from Core, and constructs the
same comparison quotient/map/multiplier from counted local kernel generators.
Every public import, existing declaration signature and visibility stays identical.
The caller docstring now describes the counted selection and open-neighbourhood
dimension transport used in its adapted proof, replacing the old prime-chain argument.
There are no edits to unrelated declarations. The original Core theorem cannot
provide the additional dimension premise: its existential conclusion only bounds
c, which can be increased by adding zero equations. Its existing private theorem for
clearing denominators is imported and applied in the caller, with the
stronger generator selection in place of the uncounted selection.
The returned duplicate private helper is deleted; Core is retained in the
import closure. No change to Core or its theorem is delivered.

Original caller against the modified dependency fails at its final application:

```
/home/ubuntu/weil-sandbox/F1/Sheaf.RingTheory.SyntomicEquationCountComparisonDimension/scratchpad/original/lean/Sheaf/RingTheory/SyntomicEquationCountComparison.lean:78:63: error: Application type mismatch: The argument
  hle
has type
  c ≤ n
but is expected to have type
  topologicalKrullDimAt ((PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)) ⟨q, ⋯⟩) =
    ↑(n - c)
in the application
  equationCount_comparison_dimension q π u hsurj hu hbij hle

(with the modules compiled into /home/ubuntu/weil-sandbox/F1/Sheaf.RingTheory.SyntomicEquationCountComparisonDimension/scratchpad/original/.lbuild) [3.0 s]
```

The modified caller and every delivered module compile in import order. This is
a forced adaptation requiring independent CODEX review. The node citer
lem-weil-pbc-syntomic-equation-count-comparison retains its statement and now
chooses the generators with the dimension count before applying transport.

## Status

landed 20261013T095949-L-2457363 2026-10-13 (merge of deliver/F1/Sheaf.RingTheory.SyntomicEquationCountComparisonDimension)
