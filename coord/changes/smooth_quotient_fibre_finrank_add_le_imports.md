# Algebra.smooth_quotient_fibre_finrank_add_le

## Reason

Remove redundant public imports while proving the theorem. No declaration signature, visibility or definition changes. Both removed modules remain publicly reachable through Mathlib.RingTheory.Smooth.Basic:

- Mathlib.RingTheory.Smooth.Basic → Mathlib.RingTheory.Unramified.Basic → Mathlib.RingTheory.Kaehler.Basic
- Mathlib.RingTheory.Smooth.Basic → Mathlib.RingTheory.Unramified.Basic → Mathlib.RingTheory.Kaehler.Basic → Mathlib.RingTheory.Ideal.Cotangent → Mathlib.Algebra.Module.SpanRank → Mathlib.LinearAlgebra.Dimension.StrongRankCondition → Mathlib.LinearAlgebra.Dimension.Finrank

## Old

```lean
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
```

## New

```lean
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
```

## Users

The table lists every transitive importer from tools/downstream.py. Only Sheaf.RingTheory.SmoothQuotientFibreFinrankAdd directly imports this module or uses its theorem; it also explicitly publicly imports both removed Mathlib modules. All public declarations remain available via the public-import paths above, so no statement meaning or proof environment changes and no adaptation is necessary. The two uses reported by --uses are the declaration in the item and its unchanged application in SmoothQuotientFibreFinrankAdd. No target definition changes or target rereview is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.PopescuLiftNilpotent | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.Paper.SmoothRetractRelativeGlobalCompleteIntersection | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.IndStandardSmooth | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuDelocalizeBase | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZero | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZeroData | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuDelocalizeWeak | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuLiftOnce | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuLiftOnceCore | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuLiftTwice | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalResolution | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.PopescuStandardNonzerodivisor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.SmoothQuotientFibreDifferentialRank | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.SmoothQuotientFibreFinrankAdd | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| Sheaf.RingTheory.SmoothStandardSmoothRetract | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| TargetsCheck | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unaffected: public import closure and theorem type unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unaffected: public import closure and theorem type unchanged. |

## Status

landed 20261013T015550-L-3019115 2026-10-13 (merge of deliver/F2/Sheaf.RingTheory.SmoothQuotientFibreFinrankAddLe)
