# AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion

## Reason

Repair coord/repairs.txt / upstream review #1424: remove the closed-immersion
wrapper duplicating Hom.isIso_residueFieldMap, and redirect both callers.
IsClosedImmersion extends SurjectiveOnStalks, so the generic theorem proves
exactly the same closed-immersion fact. No target or definition changes.

## Old

```lean
theorem Hom.isIso_residueFieldMap_of_isClosedImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) : IsIso (i.residueFieldMap z) := by
  simpa using (Hom.isIso_residueFieldMap i z)
```

## New

The duplicate declaration is removed. Its node points to the existing
AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap, whose context is
{W Z : Scheme.{u}} (p : W ⟶ Z) [SurjectiveOnStalks p]:

```lean
lemma Hom.isIso_residueFieldMap (w : W) : IsIso (p.residueFieldMap w)
```

Both callers replace the removed name with isIso_residueFieldMap and replace
the private proof import of the wrapper with the private proof import of
WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism. These are the only
changed lines in the adapted modules. The retired module has no declarations
or imports; it is retained as an empty module for the delivery protocol.

## Users

The downstream source scan lists the following modules. Only the two adapted
modules mention the removed name. Neither caller uses the removed public
imports in its signature: its own public Mathlib imports provide those types.
Transitive users keep the identical public signatures of both callers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso | C3 | Wrapper removed; node points to the existing generic theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteStalks | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion | unclaimed | Forced proof-only adaptation: direct generic import and theorem application; signature unchanged. |
| Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion | unclaimed | Forced proof-only adaptation: direct generic import and theorem application; signature unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| TargetsCheck | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No occurrence of the removed name; signatures and mathematical meaning unchanged. |

## Status

landed 20261014T023932-L-14180 2026-10-14 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso)
