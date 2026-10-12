# separableTensor_purelyInseparable_isField import visibility

## Reason

The second reading confirmed that both LinearDisjoint and Dimension.Constructions are supplied transitively by the proof-only Tower import. Their redundant direct public imports are removed. Basic supplies the public statement vocabulary. No statement, definition, or theorem visibility changes.

## Old

```lean
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
```

## New

```lean
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower
```

## Users

The source-only downstream scan lists the following modules. The only direct importer is GeometricRegularitySeparableExtension, which imports this item privately and uses only its unchanged theorem. It is compiled unchanged against the reviewed module. Since that edge is private, the removed public reexports cannot propagate through it to the remaining transitive users. Every statement retains its meaning; no target definition is changed and no adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unchanged; behind a private import edge. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.RingTheory.GeometricRegularitySeparableExtension | unclaimed | Unchanged; direct importer checked by single-file compile. |
| Sheaf.RingTheory.HenselizationPairGRing | unclaimed | Unchanged; behind a private import edge. |
| Sheaf.RingTheory.HenselizationPairGRingCore | K3 | Unchanged; behind a private import edge. |
| TargetsCheck | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | B3 | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Gabber | S2 | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged; behind a private import edge. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged; behind a private import edge. |

## Status

landed 20261012T144058-L-2090640 2026-10-12 (merge of deliver/C3/Sheaf.FieldTheory.SeparableTensorPurelyInseparable)
