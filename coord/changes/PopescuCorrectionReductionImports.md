# Sheaf.RingTheory.PopescuCorrectionReduction public imports

## Reason

The reduction proof is independent of smoothness. Replace the unused public import
of StandardSmooth by the smaller MvPolynomial.Rename module, needed by the existing
relation definition. No declaration statement, definition, universe, instance or
visibility is changed. This record documents an import-interface change only.

## Old

```lean
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
```

## New

```lean
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.MvPolynomial.Rename
```

## Users

The source-only downstream scan (`tools/downstream.py
Sheaf.RingTheory.PopescuCorrectionReduction --uses
nonempty_popescuCorrectionQuotient_reduction_equiv`) found the following 200 modules.
The sole direct importer is Sheaf.RingTheory.PopescuStandardReductionFactor. It
already has its own public import of Mathlib.RingTheory.Smooth.StandardSmooth, and
imports this item only for its proof. Thus this replacement cannot remove smoothness
names from any downstream module. The only downstream textual use of the proved
name is in that direct importer. All four definitions and the theorem signature stay
identical, so no statement changes meaning, including target statements. No forced
adaptation is needed. Claim holders below are from the local snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.PopescuLiftNilpotent | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuLiftOnce | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuLiftOnceCore | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuLiftTwice | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalResolution | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| Sheaf.RingTheory.PopescuStandardReductionFactor | unclaimed | Already publicly imports Mathlib.RingTheory.Smooth.StandardSmooth; no adaptation. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| TargetsCheck | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: sole direct importer retains its own StandardSmooth import; no adaptation. |

## Status

landed 20261013T000909-L-2282192 2026-10-13 (merge of deliver/X3/Sheaf.RingTheory.PopescuCorrectionReduction)
