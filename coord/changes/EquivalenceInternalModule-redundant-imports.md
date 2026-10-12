# Sheaf.CategoryTheory.EquivalenceInternalModule imports

## Reason

Second reading found three redundant public Mathlib imports. All three are already
available through the retained public Sheaf imports; removing the direct imports does
not change the transitive public environment, any declaration, or any target meaning.
The module compiles with just its two statement-defining Sheaf imports.

## Old

```lean
public import Sheaf.CategoryTheory.InternalModule
public import Sheaf.CategoryTheory.FiniteContinuousModule
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
```

## New

```lean
public import Sheaf.CategoryTheory.InternalModule
public import Sheaf.CategoryTheory.FiniteContinuousModule
```

## Users

All modules reported by tools/downstream.py are listed below. No downstream adaptation
is needed: the removed direct imports remain transitively public via the retained
imports. No definition used in a target changes, so semantic target review stays valid.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.Paper.GaloisLisseRepresentations | unchanged; no adaptation | Same transitive public imports and declarations. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; no adaptation | Same transitive public imports and declarations. |
| TargetsCheck | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Defs | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Inversion | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Perverse | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Properties | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; no adaptation | Same transitive public imports and declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; no adaptation | Same transitive public imports and declarations. |

## Status

landed 20261012T085305-L-25664 2026-10-12 (merge of deliver/M2/Sheaf.CategoryTheory.EquivalenceInternalModule)
