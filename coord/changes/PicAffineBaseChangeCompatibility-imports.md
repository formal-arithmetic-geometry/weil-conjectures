# pic_affine_base_change_compatibility import pruning

## Reason

The proof uses BaseChangeCurve, PicRestrictionBoundary, the new boundary transport
lemma, and Picard functoriality. The former public GenusInvariant and Picard.Jacobian
imports supply no symbol in the unchanged statement. GenusInvariant remains a proof
dependency of the new transport lemma; its mathematical role is retained.
No theorem signature, definition, or target statement changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.BaseChangeCurve
public import Sheaf.AlgebraicGeometry.GenusInvariant
public import Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Affine
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary
import Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport
```

The new module has plain proof imports of GenusInvariant, EffectiveCartier,
Picard.Degree and BaseChangeCurve.

## Users

The item has two direct importers, AffineUnitDivisorBaseChange and
Curve.KummerBaseChangeCompatibility, both using a plain import for this item.
Each already imports GenusInvariant or Picard.Jacobian explicitly as needed.
Thus no public signature or proof adaptation is needed downstream. The complete
transitive user list from tools/downstream.py is recorded below; the global build
verifies it. No other module is edited or claimed by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not modified | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not modified | unchanged signatures; no adaptation needed |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not modified | unchanged signatures; no adaptation needed |
| TargetsCheck | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Defs | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Inversion | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Perverse | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.Stalk | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not modified | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not modified | unchanged signatures; no adaptation needed |

## Status

landed 20261012T095915-L-321529 2026-10-12 (merge of deliver/N1/Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility)
