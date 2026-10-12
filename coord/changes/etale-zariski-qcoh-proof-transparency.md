# Local proof transparency commands

## Reason

The stage-3 static checker treats added `attribute` and `set_option` commands as
potential changes to what other modules see, and requires this record. These
commands only guide elaboration of the new private proof helpers and the proof
of the existing theorem. The reducibility attribute is explicitly local. No
existing declaration's signature, visibility or public definition changes; no
public import changes. This does not alter the meaning of any target and requires
no downstream adaptation. The new positive abelian comparison is a new theorem
in its own module and is documented by its new DAG node.

## Old

```lean
set_option autoImplicit false
```

There were no local tensor reducibility attributes or transparency options at
this point in the original module.

## New

```lean
set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The terminal-object proof and the generic section-unit-isomorphism proof also
locally use, scoped to their individual declarations:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

All added definitions and lemmas in the item are private and used only in proofs.
The existing theorem's signature is verbatim unchanged. The file compiles with
its actual terminal-object structure morphism, without unfolding a terminal cone.

## Users

The full transitive downstream list was obtained by `tools/downstream.py`.
Every listed module continues to import the same public interface. This record
exists for the conservative command-level static check, not for a statement or
definition modification. No source below is adapted in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | N2 | Uses the new theorem privately; existing public interface unchanged |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | P1 | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature, definition or public-import change; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature, definition or public-import change; no adaptation |
| TargetsCheck | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature, definition or public-import change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature, definition or public-import change; no adaptation |

## Status

landed 20261012T150954-L-2231233 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison)
