# StrictLocalRootDomainEtale public imports

## Reason

StrictLocalRootInvariants is unused by the item signature and repaired proof.
Replace its public re-export with the direct Henselian and AdjoinRoot public
imports needed by the unchanged signature. The new regularity and punctured-cover
proof imports are private. There is no signature or definition change and no
target semantic review is reopened.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Sheaf.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
```

## New

```lean
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Sheaf.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Ideal.GoingUp
```

## Users

Ran tools/downstream.py with --uses strict_local_root_domain_etale and --names:
139 transitive downstream modules, one direct importer, StrictLocalRootTorsorProperties.
The direct importer independently publicly imports StrictLocalRootInvariants;
therefore its full imported interface, including rotations and fixed algebras,
is preserved and no transitive user loses those definitions. Its declaration
statements remain byte for byte unchanged. Its unchanged source was compiled
against the delivered module as a temporary local check, not delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitStrictLocalOrbits | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootOrbitDescent | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorProperties | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| TargetsCheck | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition change; the only direct importer already publicly imports StrictLocalRootInvariants itself. |

## Status

landed 20261013T165639-L-1807227 2026-10-13 (merge of deliver/D2/Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootDomainEtale)
