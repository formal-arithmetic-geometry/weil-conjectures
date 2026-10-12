# Sheaf.AlgebraicGeometry.FiniteEquationsOfClosedAffine public imports

## Reason

Remove a redundant direct import. FiberDegree publicly imports Mathlib.AlgebraicGeometry.Limits,
which publicly imports Mathlib.AlgebraicGeometry.AffineScheme. Thus the same module and all its
public declarations and instances remain available downstream. No signature or definition changes,
no target meaning changes, and no forced adaptations are needed. Source inspection found one direct
importer, QuasiFiniteDegreeSublevelFiniteEquations, which also publicly imports FiberDegree itself.
The transitive users from tools/downstream.py are listed below; the retained public path proves
uniformly that their available declarations and instances do not change.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.AffineScheme
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFibreSpecialization | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteDegreeSublevelFiniteEquations | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompact | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompactAux | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: same public transitive import; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: same public transitive import; no adaptation. |
| TargetsCheck | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | No effect: same public transitive import; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: same public transitive import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: same public transitive import; no adaptation. |

## Status

landed 20261012T184309-L-4006585 2026-10-12 (merge of deliver/J1/Sheaf.AlgebraicGeometry.FiniteEquationsOfClosedAffine)
