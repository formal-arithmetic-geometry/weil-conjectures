# WeilConjectures.AlgebraicGeometry.EffectiveDescent imports

## Reason

Fpqc is needed only for the new proof, so its import must be private to the module.
Sites.Over is unused. No declaration signature or definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
```

## New

```lean
import Mathlib.AlgebraicGeometry.Sites.Fpqc
```

The Sites.Over import is removed.

## Users

Ran tools/downstream.py WeilConjectures.AlgebraicGeometry.EffectiveDescent.
There are two direct importers. Picard.Jacobian also publicly imports Picard.Degree,
which publicly imports Picard.Defs; Picard.Defs publicly imports both Mathlib modules.
The aggregate WeilConjectures independently publicly imports
WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc and
WeilConjectures.Mathlib.CategoryTheory.Sites.Over, which re-export those same modules.
Thus both direct importers retain the same exported modules and instances through
independent routes, and so do all their downstream modules listed below.
No user statement or definition changes, and no adaptation or additional claim
is needed. Group entries describe this delivery's lack of edits to those modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.GenusInvariant | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not adapted by T1 | Existing public imports retain both modules; no change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not adapted by T1 | Existing public imports retain both modules; no change. |
| TargetsCheck | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.AffineSpace | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Defs | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Inversion | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Perverse | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Properties | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted by T1 | Existing public imports retain both modules; no change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted by T1 | Existing public imports retain both modules; no change. |

## Status

landed 20261012T034515-L-1528473 2026-10-12 (merge of deliver/T1/WeilConjectures.AlgebraicGeometry.EffectiveDescent)
