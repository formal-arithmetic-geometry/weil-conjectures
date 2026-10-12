# WeilConjectures.AlgebraicGeometry.Curve.Affine import visibility

## Reason

The second-reader brief requires imports used only in proofs to be plain imports.
Six existing public imports are now plain. The public Basic and quotient imports supply
the abelian-variety commutativity and quotient instances required by the unchanged
existential statement. Curve.Kummer remains public because downstream statements and
proofs use its exported constant-sheaf comparisons and primitive-root theorem.
No declaration, target statement, or definition changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient
import Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond
import Sheaf.AlgebraicGeometry.Curve.GenericTorsionColimit
```

## Users

All six direct importers were compiled individually against the sandbox Affine module.
Every downstream module listed by downstream.py is included below. No module is adapted.
The import cleanup does not alter any object or definition used in target statements,
so it does not reopen semantic target review. The maintainer verifies the complete
library build after landing.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | Unchanged declarations and definitions; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | Unchanged declarations; compiled against sandbox Affine. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none | Unchanged declarations; compiled against sandbox Affine. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | none | Unchanged declarations; compiled against sandbox Affine. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | Unchanged declarations and definitions; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | Unchanged declarations and definitions; no adaptation required. |
| TargetsCheck | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures | none | Unchanged declarations; compiled against sandbox Affine. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | Unchanged declarations; compiled against sandbox Affine. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | Unchanged declarations and definitions; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | Unchanged declarations and definitions; no adaptation required. |

## Status

landed 20261012T044744-L-2035480 2026-10-12 (merge of deliver/H1/WeilConjectures.AlgebraicGeometry.Curve.Affine)
