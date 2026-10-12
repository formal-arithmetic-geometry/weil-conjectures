# Sheaf.RingTheory.UnramifiedSmoothConormalChartFlat imports

## Reason

Remove the redundant direct public PDeriv import. All its public declarations remain available through the unchanged public chain Smooth.Basic -> Smooth.Kaehler -> Extension.Cotangent.Basic -> Kaehler.Polynomial -> MvPolynomial.PDeriv. Existing theorem signatures and definitions are unchanged, so no target meaning or downstream statement changes. All newly added proof imports are plain imports.

## Old

```lean
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
```

## New

```lean
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
```

## Users

Source-only downstream scan of the item; every module below retains exactly the same public dependency closure. None requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.PopescuLiftNilpotent | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | C3 | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.IndStandardSmooth | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuDelocalizeBase | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZero | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZeroData | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuDelocalizeWeak | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuLiftOnce | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuLiftOnceCore | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuLiftTwice | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalResolution | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.PopescuStandardNonzerodivisor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.SmoothConormalBasisEtalePolynomialChart | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| Sheaf.RingTheory.SmoothStandardSmoothRetract | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| TargetsCheck | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: PDeriv remains public through Smooth.Basic; no adaptation. |

## Status

landed 20261012T231633-L-1961725 2026-10-12 (merge of deliver/E2/Sheaf.RingTheory.UnramifiedSmoothConormalChartFlat)
