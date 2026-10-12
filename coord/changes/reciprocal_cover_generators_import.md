# AlgebraicGeometry.Scheme.Modules.exists_line_bundle_sections_of_reciprocal_cover

## Reason

Remove the unused direct public import of Mathlib's sheaf generators module.
The unchanged public import of `Sheaf.AlgebraicGeometry.Ample` already supplies
that exact module publicly through `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.
All exported declarations and all existing signatures and definitions remain the same.
No target meaning changes or renewed statement review is needed.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.Ample
```

## New

```lean
public import Sheaf.AlgebraicGeometry.Ample
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ReciprocalCoverLineBundle --uses
exists_line_bundle_sections_of_reciprocal_cover` lists the following downstream
modules. None needs adaptation: the public import closure is identical, so every
statement, definition, and proof still has the same declarations available.
The only direct importer is `FindGloballyGenerated`; it additionally imports the
removed module itself. Its original file is compiled unchanged against the delivery.
Claims below are the local snapshot at second reading.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | N2 | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | J3 | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | P2 | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.FindGloballyGenerated | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralDimOneAmple | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged public closure; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged public closure; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged public closure; no adaptation |
| TargetsCheck | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged public closure; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged public closure; no adaptation |

## Status

landed 20261012T144121-L-2099318 2026-10-12 (merge of deliver/J2/Sheaf.AlgebraicGeometry.ReciprocalCoverLineBundle)
