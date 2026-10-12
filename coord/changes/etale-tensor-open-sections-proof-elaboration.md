# etaleTensorOpenSectionIso_component_core

## Reason

The completed proof uses local elaboration settings to keep tensor pullback folded
while composing section maps. The static interface scanner classifies additional
commands as an interface change. This record documents those commands: none changes
an existing public signature, definition body, visibility, or public import.
The private helpers and proof-only imports do not add public instance or simp rules.
No target statement, nor any definition it uses, changes meaning.

## Old

No local reducibility attributes or elaboration options in this module. Every existing
public declaration has its original signature, and both public definitions have their
original bodies.

## New

The added commands, in their order of appearance, are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The options affect elaboration of this file. The reducibility attribute is local to
its existing section and prevents expensive unfolding in the private section lemmas.
All public signatures, definitions, and visibility stay identical. Every new helper
is private and fully proved. No module is adapted.

## Users

`tools/downstream.py` reports the following transitive downstream modules. These
commands introduce no public assumptions or declarations and alter no public
statement or definition. Every listed module therefore sees the same public interface.
`--uses etaleTensorOpenSectionIso_component_core` finds only this module's own assembly.
The direct importers are `Sheaf.AlgebraicGeometry.EtaleTensorOpenSections` and
`Sheaf.AlgebraicGeometry.EtaleTensorDirectImageIdentification`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorDirectImageIdentification | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorOpenSections | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same public declarations and imports; no adaptation. |
| TargetsCheck | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same public declarations and imports; no adaptation. |

## Status

landed 20261012T223416-L-1640762 2026-10-12 (merge of deliver/S3/Sheaf.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality)
