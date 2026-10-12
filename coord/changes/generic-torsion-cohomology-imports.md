# AlgebraicGeometry.Scheme.generic_torsion_cohomology_colimit

## Reason

Prune the redundant direct public import of AlgebraicClosure after completing the proof.
No declaration signature or definition changes. The removed module remains publicly
reachable through a retained import, so every downstream declaration and target has
exactly the same meaning and access to the same algebraic-closure definitions and instances.
The import-pruning compatibility check passes. No downstream file needs adaptation.

Retained public import path:

WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion → WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint → Mathlib.AlgebraicGeometry.Sites.EtalePoint → Mathlib.FieldTheory.SeparableClosure → Mathlib.FieldTheory.SeparableDegree → Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

## Old

```lean
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
```

## New

Remove that direct line; the retained public imports still include:

```lean
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
```

## Users

All 121 downstream modules listed by `tools/downstream.py` are recorded below.
The only theorem caller is GenericTorsionColimit; its signature and invocation are unchanged.
No target definition changes, so no target statement review is reopened.
Claim holders are from this machine's current claim snapshot; none of their files is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | T1 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericTorsionColimit | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | P1 | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | Unchanged; retained public import path, no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | Unchanged; retained public import path, no adaptation. |
| TargetsCheck | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Defs | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Inversion | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Perverse | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Properties | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | Unchanged; retained public import path, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | Unchanged; retained public import path, no adaptation. |

## Status

landed 20261012T085309-L-27482 2026-10-12 (merge of deliver/N1/Sheaf.AlgebraicGeometry.Curve.GenericTorsionCohomologyColimit)
