# Algebra.popescu_auxiliaryAlgebra_localizations_part2: unused public import

## Reason

Remove the unused public import `Mathlib.RingTheory.Localization.Algebra` from
`Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart2`. The unchanged theorem
and its proof compile without it; the independent axiom check remains exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Old

```lean
public import Mathlib.RingTheory.Localization.Algebra
```

## New

The import line is removed. Every existing declaration signature is byte-for-byte
unchanged. No statement or definition is altered.

## Users

`tools/downstream.py Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart2
--uses popescu_auxiliaryAlgebra_localizations_part2` found 193 downstream modules;
the only external use of the theorem is in
`Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizations`. That module is the sole
direct importer, imports Part2 privately, and itself publicly imports
`Mathlib.RingTheory.Localization.Algebra` (line 11). Thus its own imports and
every downstream module's available public imports remain unchanged. The source
of each downstream statement is unchanged, and no target definition changes or
review reopening is needed. No adaptations are required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizations | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZero | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuDelocalizeHeightZeroData | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuHeightZeroAuxiliaryWitnesses | G2 | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| TargetsCheck | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition changes; direct importer independently imports the removed module. |

## Status

landed 20261012T184339-L-4018260 2026-10-12 (merge of deliver/R2/Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart2)
