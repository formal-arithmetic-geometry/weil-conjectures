# ArtinSchreierPullbackRows imports

## Reason

The proof needs the constant-sheaf comparison, not topological invariance or
cohomology. Import its defining module for the proof only. No declaration,
definition or target statement changes meaning. No target review is reopened.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
```

## New

```lean
import WeilConjectures.ConstructibleSheaf.Defs
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows
--uses exists_artinSchreier_pullback_rows` lists the following 105 transitive
importers. The only direct importer and only declaration user is
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows`. It already has
its own public import of TopologicalInvariance, so no transitive importer loses
access to that module. Compiled an unchanged scratch copy of that direct
importer against the delivered module using `lcompile.py --all`; both compile.
Every existing declaration's signature and all definitions are unchanged.
No module is adapted or requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| TargetsCheck | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged; direct importer independently publicly imports TopologicalInvariance. |

## Status

landed 20261013T082337-L-1632826 2026-10-13 (merge of deliver/D4/Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows)
