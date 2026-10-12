# SteinFactorizationAffine proof import

## Reason

The source GammaSpecAdjunction module is used only for the proof's Stein factorization identity. The signature uses the Mathlib GammaSpecAdjunction definitions. Narrow the source import as required by the stage-3 brief; no declaration or definition changes.

## Old

```lean
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
```

## New

```lean
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
```

## Users

Both direct importers import this module privately, so this change does not propagate through their public exports. HenselianConnectedness itself imports the source GammaSpecAdjunction publicly. No downstream declaration changes meaning, and no adaptations are delivered. The table records every module returned by tools/downstream.py; holders need no edits.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not queried; no edit | No statement or definition change; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not queried; no edit | No statement or definition change; no adaptation. |
| TargetsCheck | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Defs | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not queried; no edit | No statement or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not queried; no edit | No statement or definition change; no adaptation. |

## Status

landed 20261012T150949-L-2229367 2026-10-12 (merge of deliver/B2/Sheaf.AlgebraicGeometry.SteinFactorizationAffine)
