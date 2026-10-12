# AlgebraicGeometry.affine_unit_divisor_base_change

## Reason

LocalDvrBaseChange is a proof dependency, not a requirement of the theorem signature.
Its original public import leaks proof declarations through the item. Move it to the new
core module as a plain import. The other removed imports were already private proof
imports. The new core and descent public imports contain only their signature needs;
planned proof ingredients are plain imports. No existing declaration signature, definition,
or target meaning changes. No adaptation is necessary.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.LocalDvrBaseChange
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.GenusInvariant
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
```

## New

```lean
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore
import Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent
import Sheaf.AlgebraicGeometry.BaseChangeCurve
```

## Users

Read tools/downstream.py output for the item and searched all 111 transitive downstream
modules for local_dvr_base_change and ord_eq_of_stalk_uniformizer: no uses. The only direct
importer is UnitsQuotientBaseChange; it uses affine_unit_divisor_base_change, whose signature
is unchanged. A scratch copy of that original file compiles without warnings against the
sandbox's compiled overlay, which contains the new interface. No downstream module's
statement or definition uses either removed proof declaration; all types and meanings stay
unchanged. Group ownership below is from the local claims snapshot, not a new claim.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed in local snapshot | Original compiles against changed overlay; theorem signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | No use of removed proof declarations; signatures and definitions unchanged; no adaptation. |

## Status

landed 20261012T150954-L-2231133 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange)
