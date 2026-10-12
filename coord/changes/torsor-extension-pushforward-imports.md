# TorsorExtensionPushforward imports

## Reason

The proof treats the underlying closed embedding directly, using stalkwise detection,
instead of transporting a scheme morphism to the closed-subset inclusion in
`Sheaf.Topology.ClosedImmersionPushforwardExact`. Its theorem and its proof-only
closed-subset stalk module are unnecessary on this edge. The replacement public Mathlib
import supplies the abelian sheaf category and the short exact sequence vocabulary used
in the unchanged statement. All added imports of proof tools are private.

## Old

```lean
public import Sheaf.Topology.ClosedImmersionPushforwardExact
```

## New

```lean
public import Mathlib.Topology.Sheaves.Abelian
```

## Users

The following is the full transitive list from `tools/downstream.py`.
The sole direct importer, `Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestriction`,
does not use the removed closed-subset exactness declaration. It imports
`Sheaf.Topology.ClosedPushforwardBoundaryNaturality` independently, which still imports
that module. Its original source is compiled against this delivery's overlay.
No signature, definition, instance, or target meaning changes. No adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | N2 | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.PicardLift | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Import pruning only; signatures and meanings unchanged. |
| Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestriction | S1 | Import pruning only; signatures and meanings unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Import pruning only; signatures and meanings unchanged. |
| TargetsCheck | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Import pruning only; signatures and meanings unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Import pruning only; signatures and meanings unchanged. |

## Status

landed 20261012T150953-L-2230930 2026-10-12 (merge of deliver/J3/Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward)
