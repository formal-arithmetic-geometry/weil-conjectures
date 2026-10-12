# Sheaf.ConstructibleSheaf.MonoidalParts imports

## Reason

The second-reading brief requires imports used only by proofs to be plain imports.
The geometric-stalk tensor comparison is used only in the finiteness proof.
Expose the monoidal structure required by the unchanged theorem signatures through
its defining module instead. Neither theorem signature nor any definition changes.
The sole direct importer, `WeilConjectures.ConstructibleSheaf.Monoidal`, independently
publicly imports `StalkMonoidal`, so all downstream declarations retain that API.
No downstream module needs adaptation or is changed in this delivery.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
```

## New

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
```

## Users

All transitive downstream modules reported by
`tools/downstream.py Sheaf.ConstructibleSheaf.MonoidalParts --uses sheafFiberTensorIso --names`
are listed below. Their statements and definitions do not change: the sole direct importer
retains its independent public import. Claim groups are those in the read-only snapshot.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleFilteredData` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeBiproductAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `TargetsCheck` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.ConstructibleSheaf.FreeLifting` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.ConstructibleSheaf.Monoidal` | none | Already explicitly imports StalkMonoidal publicly; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.AffineSpace` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.ArtinSchreier` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.ArtinSchreierCohomology` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Defs` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Inversion` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Perverse` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Properties` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModelReduction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unknown | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | none | No signature or definition change; direct importer retains public StalkMonoidal. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | none | No signature or definition change; direct importer retains public StalkMonoidal. |

## Status

landed 20261012T070528-L-3466837 2026-10-12 (merge of deliver/B3/Sheaf.ConstructibleSheaf.MonoidalParts)
