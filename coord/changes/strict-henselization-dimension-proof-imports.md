# Algebra.ringKrullDim_eq_of_isStrictHenselization

## Reason

The conservative static interface check detects the added `open` command and
private helper options as a lexical command change. The command opens category
names for elaboration inside this file; it adds no public definition, instance,
notation, or attribute. The two transparency options are scoped to a private
helper. This record documents that finding, not a mathematical interface change.

## Old

```lean
universe u

namespace Algebra
```

## New

```lean
universe u

open CategoryTheory CategoryTheory.Limits
```

Private helper declarations intervene before `namespace Algebra`. The main theorem
signature and its existing visibility are identical. Added proof imports are all
non-public, and every new declaration is private. No adaptation is needed.

## Users

The table lists the full downstream module closure from `tools/downstream.py`.
Its `--uses` output finds only the declaration's own module as a textual exact-name
use, since downstream references may use shorter names.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | B2 | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No public signature or definition changes; proof-only helpers. |
| Sheaf.RingTheory.StrictHenselizationRegular | M4 | No public signature or definition changes; proof-only helpers. |
| TargetsCheck | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No public signature or definition changes; proof-only helpers. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No public signature or definition changes; proof-only helpers. |

## Status

landed 20261013T181115-L-2604958 2026-10-13 (merge of deliver/M4/Sheaf.RingTheory.StrictHenselizationDimension)
