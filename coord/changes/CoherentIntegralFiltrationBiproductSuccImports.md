# CoherentIntegralFiltrationBiproductSucc imports

## Reason

Remove a redundant public import while proving the existing theorem. The
public statement depends only on CoherentIntegralFiltration, which already
exports all its signature dependencies. Compilation without Noetherian
confirms the item needs neither its definitions nor its instances separately.
The closure theorem needed by the proof is imported privately.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum
```

No existing declaration signature or definition changes.

## Users

`tools/downstream.py` lists 265 transitive importers at review time. The only
direct importer is `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumStep`.
It imports the item proof-only and publicly imports Noetherian itself. Thus it
retains its full original environment, and the item's unchanged declaration has
exactly the same type. All further downstream environments and statements are
unchanged. The direct importer was compiled unchanged against the sandbox's
compiled replacement module (scratch copy, not delivered). No target meaning
changes and no forced adaptations are required. The following groups are from
the read-only claims snapshot; the same argument applies to every transitive
importer.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationGenericStep | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSum | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumStep | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissage | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleConstructibleReflection | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleGenericReflection | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleLocallyConstantStrata | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeModuleFiniteOpenAssertionsTransfer | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteNoetherianSchemeSplitting | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitReductionSpectrumComponents | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No semantic effect; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No semantic effect; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No semantic effect; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No semantic effect; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No semantic effect; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No semantic effect; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No semantic effect; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No semantic effect; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No semantic effect; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No semantic effect; no adaptation. |
| TargetsCheck | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No semantic effect; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No semantic effect; no adaptation. |

## Status

landed 20261013T022413-L-3213195 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationBiproductSucc)
