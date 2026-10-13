# SmoothSectionPowerSeriesChart public imports

## Reason

Remove three redundant direct public imports while preserving every public dependency:
Mathlib.AlgebraicGeometry.Morphisms.Smooth publicly imports Noetherian and Flat;
Flat publicly imports RingHom.FaithfullyFlat, which exports RingHom.Flat. Smooth's
public transitive closure also includes LocalRing.RingHom.Basic. Read the public
import graph in the pinned Mathlib source tree to verify all three paths. No
statement, definition, or elaborated target meaning changes. The preflight requires
this record for public-import removal even when its public transitive closure is
unchanged. All downstream statement dependencies therefore remain available.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Basic
```

The two additional Sheaf imports are plain imports, used only by the proof.
The redundant Noetherian import is also absent in both new modules and the
redundant LocalRing.RingHom.Basic import is absent in the new generic-image module.

## Users

`tools/downstream.py` reports the following transitive downstream modules. No
signature changes, adaptations, or renewed target meaning review are needed,
because the public dependency closure and all definitions are unchanged. The
only direct importer is ClosedFiberPowerSeriesTest, which imports this module
only for its proof. Attempting to compile an unchanged scratch copy against the
overlay stopped on a missing baseline artifact for
Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection, before checking
this import; no failure is attributed to the public-import pruning. The public
import-graph check, rather than that unavailable downstream compile, establishes
preserved availability.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition changes; same publicly available dependencies. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition changes; same publicly available dependencies. |
| TargetsCheck | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition changes; same publicly available dependencies. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition changes; same publicly available dependencies. |

## Status

landed 20261013T100108-L-2481022 2026-10-13 (merge of deliver/R1/Sheaf.AlgebraicGeometry.Morphisms.SmoothSectionPowerSeriesChart)
