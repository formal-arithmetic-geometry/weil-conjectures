# AlgebraicGeometry.higherDirectImageSheafifiedPresheaf

## Reason

`PlusSingle` provides only the final comparison used in the proof. The module-system
contract requires a plain import for proof-only dependencies. This is an import visibility
correction, with no statement or definition change. The two direct importers import this
module with plain `import`, and use none of the PlusSingle declarations. The downstream
search for `homologyRightDerivedFunctorPlusObjSingleFunctorIso` finds zero users. Neither
direct importer reexports this module. No target meaning changes or target review reopens.

## Old

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
```

## New

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
```

## Users

All 116 transitive downstream modules reported by `tools/downstream.py
Sheaf.Paper.HigherDirectImageSheafifiedPresheaf --uses
homologyRightDerivedFunctorPlusObjSingleFunctorIso` are included below. The direct importers
are `Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic` and
`Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange`; their statements and definitions
are unchanged by this correction. Other modules' files were not changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange | R2 | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | No declaration type or definition changes; no adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | No declaration type or definition changes; no adaptation required. |
| TargetsCheck | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | No declaration type or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | No declaration type or definition changes; no adaptation required. |

## Status

landed 20261012T085247-L-17972 2026-10-12 (merge of deliver/H2/Sheaf.Paper.HigherDirectImageSheafifiedPresheaf)
