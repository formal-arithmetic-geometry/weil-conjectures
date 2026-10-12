# DescendFlatFinitePresentation public limit import

## Reason

The second reading proved the geometric comparison using the existing
AffineOpenDirectedRingSystem and AffineChartTensorComparison modules. The item no
longer uses LimitAffineTransition, and its statement uses only Mathlib scheme,
flatness, finite-presentation and over-pullback declarations. Remove the unused
public proof dependency as required by the stage-3 brief. No target statement,
existing declaration signature, or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

The import is removed. The remaining public imports supply the existing signature.

## Users

Read-only tools/downstream.py found the following transitive importers. No importer
mentions exists_limit_affine_transition_core, limit_affine_transition_affine_comparison,
or exists_limit_affine_transition;
there is no declaration or definition adaptation. The direct importer
DescendFiniteLocallyFree already imports the source AffineTransitionLimit module
and is compiled against this delivery's overlay to verify its imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleFibreSpecialization | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification | ORCHESTRA | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts | N2 | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| TargetsCheck | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Gabber | S2 | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | No declaration or definition changed; no use of the removed module's declarations. |

## Status

landed 20261012T123739-L-1129488 2026-10-12 (merge of deliver/P2/Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation)
