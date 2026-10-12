# Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite public imports

## Reason

Remove the unused direct public Etale import as required by stage-3 pruning.
No declaration signature or definition changes. The sole direct importer,
Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite, imports this module only
for its proof and independently publicly imports Mathlib.AlgebraicGeometry.Morphisms.Etale.
Its public statements and proof therefore keep the same Etale declarations and instances.
This independent public route also covers all transitive importers. None needs adaptation,
and no target meaning changes or semantic review reopens.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
```

## New

This direct import is removed. All other original public imports are retained.
The two added Sheaf imports and two retained Sheaf proof imports are proof-only
and do not change what importers see.

## Users

Complete transitive list from `tools/downstream.py` (161 modules).
The sole direct importer's source was read and its independent public Etale import verified.
Groups are from available local claim records; no claimed module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | T1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | M1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange | P1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | T1 | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| TargetsCheck | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Defs | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Properties | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none recorded | Etale remains public at the sole direct importer; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none recorded | Etale remains public at the sole direct importer; no adaptation. |

## Status

landed 20261012T070532-L-3468834 2026-10-12 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite)
