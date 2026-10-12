# SpecStalkLimitAffineNeighbourhoods public imports

## Reason

The complete proof uses Mathlib only. Remove the unfinished canonical-morphism module
and the unused module-stalk proof import. The statement's stalk and canonical maps are
already defined in Mathlib.AlgebraicGeometry.Stalk. No definition or theorem signature changes.
The open command adds Limits and Opposite for the categorical construction.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.Topology.PresheafModuleStalkFunctor
open CategoryTheory TopologicalSpace
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Filtered.Final
open CategoryTheory Limits Opposite TopologicalSpace
```

## Users

The downstream scan lists the following modules. No module needs adaptation or a claim:
no statement or definition changes, and the import-pruning check returns exit code 0.
The public theorem has no textual downstream users yet. Target meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.GabberCriterion | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.GabberCriterionDegree | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.GabberPrincipalClassLocallyZero | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none required | Same statements; no lost declaration use found by import_prune_check. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| TargetsCheck | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.AffineSpace | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Defs | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Inversion | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Perverse | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Properties | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.FourierTransform.Properties.Stalk | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Gabber | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none required | Same statements; no lost declaration use found by import_prune_check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none required | Same statements; no lost declaration use found by import_prune_check. |

## Status

landed 20261012T095922-L-323915 2026-10-12 (merge of deliver/R3/Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods)
