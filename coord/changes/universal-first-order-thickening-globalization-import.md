# UniversalFirstOrderThickeningAffineGlobalization public import

## Reason

Remove an unused public import from the proved globalization module. Neither its
statement nor its proof uses formally unramified morphisms. The only direct
importer, Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExistence, already
publicly imports Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified on line 3.
Therefore every downstream module retains the same available declarations and
instances through that importer. No downstream source requires adaptation, and
no target statement or definition changes. import_prune_check.py passes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening
```

## New

```lean
public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening
```

## Users

All transitive downstream modules reported by tools/downstream.py are listed.
The shared effect follows from the sole direct importer's explicit public import;
none of these modules is edited or needs a forced adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ArtinianLiftingFromEtaleInfinitesimal | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoodsPointwise | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.EtaleOfInfinitesimalRestrictionsProper | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FlatOpenDiagonalConormalZero | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.OpenIsoConormalZero | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExistence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestrictionConormal | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| TargetsCheck | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No change: the sole direct importer publicly imports FormallyUnramified itself. |

## Status

landed 20261013T010624-L-2674387 2026-10-13 (merge of deliver/W4/Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningAffineGlobalization)
