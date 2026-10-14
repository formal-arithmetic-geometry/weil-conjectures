# MapExtendHomology public import pruning

## Reason

Second reading found two redundant direct public imports. The reduced module
compiles and retains the exact public theorem signature. The only direct importer,
Sheaf.Paper.FreeRepresentableHomotopyHomology, imports this module privately and
itself publicly imports Embedding.CochainComplex. Thus removal does not change any
public signature or definition in the downstream import closure. No target meaning
changes, and no downstream adaptation is needed.

## Old

```lean
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
```

## New

```lean
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
```

The proof-only upstream import replaces the three private duplicates as documented
in the existing landed coord/changes/map-extend-homology.md. No existing public
signature or definition changes. The private declarations have no external users.

## Users

The following table lists every module reported by tools/downstream.py, plus the
item itself. Group holdings are the local coordination snapshot; none is adapted.
The theorem has just one downstream textual user, FreeRepresentableHomotopyHomology.
Its unchanged public statements shield all later users from the import pruning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.MapExtendHomology | Y3 | Direct import pruning; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyBaseChangeSquare | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyPullbackComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorKernel | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveScalarBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.EtaleObjectCohomologyStalkComplex | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.FreeRepresentableHomotopyHomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.GabberCriterion | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsAffineVanishing | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsComparisonMap | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsDescentEquality | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsDescentSections | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ObjectCohomologyPresheafResolution | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.PushedResolutionPositiveHomologyZero | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.StrictHenselianCohomologyLocallyZero | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparisonIso | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsEpi | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleCanonicalLeray | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtalePushedResolution | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtalePushedResolutionQuasiIso | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleEquivalences | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionComparisonExists | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists | unclaimed | No signature or definition changes; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionMap | unclaimed | No signature or definition changes; no adaptation. |
| TargetsCheck | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature or definition changes; no adaptation. |

## Status

landed 20261014T001738-L-2556769 2026-10-14 (merge of deliver/Y3/Sheaf.CategoryTheory.MapExtendHomology)
