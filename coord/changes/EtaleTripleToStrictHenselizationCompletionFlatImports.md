# EtaleTripleToStrictHenselizationCompletionFlat imports

## Reason

The original theorem uses only the residue triple definitions, not the strict
henselization triples theorem. Import its definition module directly to remove an
unused public proof dependency, as required by the second-reading brief. No existing
signature, definition, or proof in another module is changed.

## Old

```lean
public import Sheaf.RingTheory.StrictHenselizationTriples
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
```

## Users

`tools/downstream.py Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat
--uses strictHenselization_triples` listed the following transitive users and found
zero uses of the removed theorem. The sole direct importer is
`Sheaf.RingTheory.PointedEtaleCompletionStageFlat`, which imports the item privately,
so the removed re-export cannot propagate through it to other modules. Its signature
uses only its own public imports; its proof is currently sorry. It is compiled
unchanged against this delivery as an additional check. No target meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | V3 | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.PointedEtaleCompletionStageFlat | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlat | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationCompletionNoetherian | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationNoetherian | unclaimed | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.StrictHenselizationRegular | unclaimed | No statement or definition changes; no adaptation. |
| TargetsCheck | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition changes; no adaptation. |

## Status

landed 20261013T162413-L-1520411 2026-10-13 (merge of deliver/W3/Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat)
