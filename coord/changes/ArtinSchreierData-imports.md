# AlgebraicGeometry.artinSchreier_data (imports and local linter command)

## Reason
Remove the redundant public ShortExact import and unused proof imports. ShortExact
remains publicly available through the retained Kummer import, which publicly imports
that same module. Silence the unused-variable linter locally because the original
existential binder hzero is intentionally unused in the following proposition. Its
name and the full theorem signature remain byte for byte unchanged.

## Old
```lean
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
```
The theorem previously had no local linter option.

## New
The redundant public import is removed; the retained public Kummer import exports
ShortExact. Immediately before the original docstring:
```lean
set_option linter.unusedVariables false in
```
Proof imports now name the two new reduction modules. No existing definition or
statement is changed; no target meaning changes or renewed target review is required.

## Users
The following are all transitive importers in this checkout, including target checks.
The removed import is still exported through Kummer, so none needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ArtinSchreierExact | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.ArtinSchreierSequence | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; no adaptation | No declaration or export lost; local lint only. |
| TargetsCheck | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Defs | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Inversion | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Perverse | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Properties | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; no adaptation | No declaration or export lost; local lint only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; no adaptation | No declaration or export lost; local lint only. |
| Sheaf.AlgebraicGeometry.ArtinSchreierDataConstruction | K1 | New module: natural section identification only. |
| Sheaf.AlgebraicGeometry.ArtinSchreierDataFormulas | K1 | New module: constructs maps for natural section identifications. |

## Status
landed 20261012T060743-L-2910060 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ArtinSchreierData)
