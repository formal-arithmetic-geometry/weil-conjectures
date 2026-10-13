# exists_affine_locally_free_model_core import pruning

## Reason

Sheaf.AlgebraicGeometry.Morphisms.AffineLocallyFreeModelCore does not use Stalk.
Its sole direct importer, Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel,
already has `public import Mathlib.Algebra.Category.ModuleCat.Stalk` independently.
Removing this unused public import therefore preserves that importer's exported API.
A duplicate public Modules.Sheaf import and redundant private LocallyFree import are
also removed. The three new imports are proof-only. The repair reuses the existing private
finitePresentation_overEquiv_inverse theorem via import all; no dependency
interface is changed. Every existing declaration signature,
visibility, definition, and target statement remains unchanged. No module is adapted.

## Old

```lean
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

## New

```lean
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Sheaf.AlgebraicGeometry.PerfectNoetherianCohomology
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
```

## Users

The direct importer independently provides the removed public import. All 132 transitive
importers listed by tools/downstream.py are below; none requires a source adaptation.
Claim holders were read from coord/claims at preparation time. The unchanged direct
importer compiled against the sandbox core in 13.9 seconds without warnings; its
source copy is scratch material, not an adapted delivery module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel | unclaimed | Already publicly imports Stalk directly; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesTestFiniteExtensionFlat | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| TargetsCheck | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged statements; Stalk remains exposed by the direct importer. |

## Status

landed 20261013T130752-L-3986726 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.Morphisms.AffineLocallyFreeModelCore)
