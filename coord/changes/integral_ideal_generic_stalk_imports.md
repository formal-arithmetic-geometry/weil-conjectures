# AlgebraicGeometry.Scheme.integral_ideal_generic_stalk

## Reason

`Mathlib.AlgebraicGeometry.FunctionField` is used only for the proof's field instance,
so make that import private as required by the module-system convention. Remove the
unused private `Sheaf.Topology.PresheafModuleStalkFunctor` import. Neither declaration
signatures nor definitions change. All five direct importers import this item privately;
therefore they did not expose its function-field reexports in their public signatures.
Only CoherentGenericPointIdealInclusion mentions functionField, and it already publicly
imports Mathlib.AlgebraicGeometry.FunctionField itself. No forced adaptations are needed.
The theorem and the definitions it uses keep the same mathematical meaning; no target
statement or target-dependent definition changes, so no target statement review reopens.

## Old

```lean
public import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.Topology.PresheafModuleStalkFunctor
```

## New

```lean
import Mathlib.AlgebraicGeometry.FunctionField
```

## Users

All modules returned by `tools/downstream.py` are recorded below. The change affects
only visibility of a proof dependency; all statements and definitions keep their meaning.
Direct importers are checked in scratch copies against the delivered modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | N1 | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion | unclaimed | Private importer; no signature/definition change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissage | unclaimed | Private importer; no signature/definition change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | unclaimed | Private importer; no signature/definition change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport | V1 | Private importer; no signature/definition change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible | unclaimed | Private importer; no signature/definition change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | R2 | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.SplitReductionSpectrumComponents | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Indirect user; no signature/definition change. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Indirect user; no signature/definition change. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Indirect user; no signature/definition change. |
| TargetsCheck | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Indirect user; no signature/definition change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Indirect user; no signature/definition change. |

## Status

landed 20261012T184346-L-4020865 2026-10-12 (merge of deliver/T1/Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk)
