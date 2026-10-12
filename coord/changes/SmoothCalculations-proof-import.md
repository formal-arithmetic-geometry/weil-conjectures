# SmoothCalculations proof import

## Reason

`CohomologicalDimension` supplies vanishing theorems and a topological lemma used
only by proofs. The second-reading brief requires proof imports to be private.
The public `Assertions` and `SmoothBaseChange.Defs` imports already supply every
object in the unchanged declaration signatures. No declaration, definition,
instance, target statement, or unit route is changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
```

## Users

Source-only `tools/downstream.py` lists the 100 modules below. Checked their direct
imports and public import closures with the proposed edge removed: 99 retain
visibility of all source modules independently. The remaining module,
`Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction`, uses only
its own direct dependencies (including `Curve.Reductions` for the transfer
theorem); its signatures and definition use retained public imports. A scratch
copy compiled cleanly against the modified module to verify this case. Public
Mathlib remains available through `SmoothBaseChange.Defs`. No adaptation is
needed. All statements keep their meaning, including the target statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not modified | unchanged declarations; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not modified | unchanged declarations; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not modified | unchanged declarations; no adaptation |
| TargetsCheck | not modified | unchanged declarations; no adaptation |
| WeilConjectures | not modified | unchanged declarations; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not modified | unchanged declarations; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Defs | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Inversion | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Properties | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not modified | unchanged declarations; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not modified | unchanged declarations; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not modified | unchanged declarations; no adaptation |

## Status

landed 20261012T085218-L-5119 2026-10-12 (merge of deliver/C1/WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations)
