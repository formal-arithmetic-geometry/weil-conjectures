# exists_square_zero_tensor_boundary_leibniz elaboration settings

## Reason

The proof needs local irreducibility of the cohomology and comparison constructions,
and transparency-respecting elaboration, to prevent expensive unfolding. All declaration
signatures, universes, and public imports are identical. The irreducibility attributes are
local and the options govern elaboration in this file only. No downstream module is adapted.
The mechanical checker classifies these file commands as an interface change.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] RingedSpace.moduleCohomology
  RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons
```

## Users

The theorem's only direct declaration user is SquareZeroTensorPowerBoundary. Its signature
and meaning are identical. The following complete downstream module inventory is unaffected:
these settings and local attributes do not propagate to importers. No target definition or
statement changes, and no renewed target statement review is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Identical signature; local settings do not propagate. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Identical signature; local settings do not propagate. |
| TargetsCheck | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Identical signature; local settings do not propagate. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Identical signature; local settings do not propagate. |

## Status

landed 20261013T072401-L-1123526 2026-10-13 (merge of deliver/P1/Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz)
