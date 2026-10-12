# Sheaf.AlgebraicGeometry.DescendAffine public imports

## Reason

The proof uses the existing fixed-target affine-limit theorem. The former public import
of LimitAffineTransition is unused. Import Mathlib directly for the unchanged statement.
Only exports are pruned: no theorem signature or definition is changed. None of the 271
textual downstream modules mentions the three declarations of LimitAffineTransition
(`tools/downstream.py --uses` checked all three). No adaptation is needed. The global
build remains the final check of implicit elaboration effects.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
```

## New

```lean
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.EventuallyAffine
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ChowFiniteType | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DescendClosedImmersion | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DescendFinite | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFibreSpecialization | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.EventuallyProper | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperLimitNoetherian | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportDescent | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | no adaptation | No use of removed exports; statement unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | no adaptation | No use of removed exports; statement unchanged. |
| TargetsCheck | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Defs | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Inversion | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Perverse | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Properties | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | no adaptation | No use of removed exports; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | no adaptation | No use of removed exports; statement unchanged. |

## Status

landed 20261012T070550-L-3476959 2026-10-12 (merge of deliver/S1/Sheaf.AlgebraicGeometry.DescendAffine)
