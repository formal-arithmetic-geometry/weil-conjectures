# AlgebraicGeometry.Scheme.surjective_sections_of_cech_h1_vanishing

## Reason

Repair of reviewer X-b2afc point H9: remove two redundant public imports.
The corrected module compiles cleanly. Both removed modules remain in the public-import
closure of the retained imports, so no declarations or instances become unavailable.
The theorem signature and definitions are unchanged; no target meaning changes.

## Old

```lean
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
```

## New

Both import lines are deleted. Retain the public imports of AffineEtale,
ShortComplex.HomologicalComplex, and SheafCohomology.Cech.

## Users

All transitive downstream modules reported by tools/downstream.py are listed below.
No module requires adaptation because the public-import closure retains both modules.
The sole direct importer uses the unchanged theorem in its proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1 | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | Q1 | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| TargetsCheck | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | T1 | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unaffected: both removed imports remain publicly available transitively; theorem unchanged. |

## Status

landed 20261012T025240-L-1234414 2026-10-12 (merge of deliver/V1/Sheaf.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1)
