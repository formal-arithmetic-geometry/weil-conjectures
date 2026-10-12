# AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point

## Reason

Remove a redundant direct public import. Mathlib.RingTheory.Length publicly imports
Mathlib.RingTheory.FiniteLength, which publicly imports Mathlib.RingTheory.Artinian.Module.
Thus this removal changes no exported declaration, instance, definition, theorem statement,
or target meaning. The delivery gate requires a record for any removed public import.

## Old

```lean
public import Mathlib.RingTheory.Artinian.Module
```

## New

The direct import is removed; `public import Mathlib.RingTheory.Length` remains.
All existing declaration signatures and definitions remain byte-for-byte unchanged.

## Users

The complete downstream list from tools/downstream.py is below. For each module,
the public import closure still contains exactly the same modules: the removed edge
is supplied by the public Length -> FiniteLength -> Artinian.Module path. Hence all
statements, definitions, instances, and proofs retain the same imported environment.
No adaptation is required. Groups are from the repository's current claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoodsPointwise | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.EtaleOfInfinitesimalRestrictionsProper | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged; identical transitive public imports |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | unchanged; identical transitive public imports |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | unchanged; identical transitive public imports |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | unchanged; identical transitive public imports |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | unchanged; identical transitive public imports |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | unchanged; identical transitive public imports |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | unchanged; identical transitive public imports |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | unchanged; identical transitive public imports |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | unchanged; identical transitive public imports |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged; identical transitive public imports |
| TargetsCheck | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged; identical transitive public imports |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged; identical transitive public imports |

## Status

landed 20261012T184357-L-4024847 2026-10-12 (merge of deliver/X2/Sheaf.AlgebraicGeometry.SmoothArtinianLiftingAtPoint)
