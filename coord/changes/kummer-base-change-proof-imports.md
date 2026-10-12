# AlgebraicGeometry.kummer_base_change_compatibility imports

## Reason

Second reading removes unused broad imports and makes proof dependencies private.
The theorem signature and every definition remain byte for byte unchanged.
This records the exported-import adjustment required by stage-3 preflight.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import Sheaf.AlgebraicGeometry.GmPicardPullback
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Curve.Brauer
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.GmPicardPullback
import Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
```

## Users

All three direct importers use a plain import: ConstantKummerNaturality,
ConstantLowDegreeBaseChange, and RootTrivializationBaseChange. Their signatures use
curve, Kummer, Gm/Picard, and inverse-image declarations provided by their own imports
or the retained signature imports. None uses the removed comparison proof lemmas in
its statement or defining data. Each is compiled in a scratch copy against the revised
sandbox modules. The plain imports form a visibility barrier for all further users.
No target statement or defining data changes; no target semantic review is reopened.
No dependent module requires adaptation. The full current transitive downstream list follows.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Direct plain importer; checked signature and scratch compile; unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | Direct plain importer; checked signature and scratch compile; unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | T1 | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | P1 | Direct plain importer; checked signature and scratch compile; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No semantic change; direct plain-import visibility barrier. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No semantic change; direct plain-import visibility barrier. |
| TargetsCheck | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No semantic change; direct plain-import visibility barrier. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No semantic change; direct plain-import visibility barrier. |

## Status

landed 20261012T070545-L-3474868 2026-10-12 (merge of deliver/P1/Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility)
