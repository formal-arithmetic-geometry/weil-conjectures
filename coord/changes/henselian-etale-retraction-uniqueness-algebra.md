# algHom_eq_of_henselianLocalRing_etale

## Reason

The original Lean signature uses an independent Algebra S B instance, although étaleness
and the residue-field hypotheses refer to phi. That statement is false. Let
S=B=k⊕V be the square-zero extension of a field k by a vector space with basis e_n
(n∈N). Its maximal ideal V is square-zero, so S is a henselian local ring. Take phi=id
and q'=V. The independent algebra structure fixes k and sends e_n to e_(n+1).
Two retractions of this structure send e_(n+1) to e_n, but send e_0 respectively to 0
and e_0. They are distinct ring maps (multiplication on V is zero), and both have
maximal-ideal preimage V since they fix k. Meanwhile phi is étale and its residue-field
map is the identity. Thus all original hypotheses hold but uniqueness fails.

Stacks Project Tag 04GG(8) concerns retractions of the given ring map. Bind the algebra
structure to phi.toAlgebra, as the caller and the existence theorem already do. The DAG's
natural-language statement and all target statements remain unchanged.
Source checked: https://stacks.math.columbia.edu/tag/04GG, statement (8), proof of (1)⇒(8).

## Old

```lean
theorem algHom_eq_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm))
    [Algebra S B] (σ τ : B →ₐ[S] S)
    (hσ : (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q')
    (hτ : (IsLocalRing.maximalIdeal S).comap τ.toRingHom = q') : σ = τ
```

## New

```lean
theorem algHom_eq_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∀ (σ τ : B →ₐ[S] S),
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' →
      (IsLocalRing.maximalIdeal S).comap τ.toRingHom = q' → σ = τ
```

## Users

`tools/downstream.py Sheaf.RingTheory.HenselianEtaleRetractionUniqueness --uses
algHom_eq_of_henselianLocalRing_etale` found 242 downstream modules and only one actual
caller (besides the declaration itself). The caller was compiled against the new module
without modifying its source. All other downstream modules have no occurrence of the
changed declaration, and its proof-only import is not exposed to them.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.HenselianEtaleRetraction | none; unchanged | Already installs phi.toAlgebra; the existing call compiles unchanged. Its statement is unchanged. |
| Sheaf.RingTheory.HenselianEtaleRetractionUniqueness | M3 | Correct the algebra-map type and close its sole sorry. |

No definition changes, so target meanings do not change and no target definition review reopens.

### Complete downstream inventory (second reading)

Sources and claims checked on 2026-10-12. This lists every transitive importer reported
by downstream.py, including modules that do not call the changed declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | K2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | G1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | S1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | U1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | ORCHESTRA | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalkAux | G2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer | K2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleInjective | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteLift | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteSection | B2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberH0ProjectionRestrictions | B2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.IntegralPointedClopenRefinement | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | ORCHESTRA | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | F1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No use of changed declaration; source and statements unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.EtaleTripleStrictHenselizationIdentification | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.FiniteLocalHenselian | H2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.FiniteOverHenselianLocalProduct | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.HenselianEtaleRetraction | none recorded | Uses phi.toAlgebra; caller compiled unchanged; statement unchanged. |
| Sheaf.RingTheory.HenselianFiniteEtaleEquivalence | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.HenselianPairApproximation | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.MapIntoHenselianColimit | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.PopescuEnlargeSolutionModulo | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.PopescuResolveCharP | V2 | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.PopescuSmoothing | A3 | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.PopescuSolutionModulo | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.PopescuSolutionModuloChoose | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlat | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.StrictHenselizationCompletionNoetherian | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.StrictHenselizationNoetherian | none recorded | No use of changed declaration; source and statements unchanged. |
| Sheaf.RingTheory.StrictHenselizationRegular | none recorded | No use of changed declaration; source and statements unchanged. |
| TargetsCheck | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Defs | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Inversion | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Perverse | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Properties | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | S2 | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | J2 | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.Integral.Exact | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none recorded | No use of changed declaration; source and statements unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none recorded | No use of changed declaration; source and statements unchanged. |

## Status

landed 20261012T113948-L-821662 2026-10-12 (merge of deliver/M3/Sheaf.RingTheory.HenselianEtaleRetractionUniqueness)
