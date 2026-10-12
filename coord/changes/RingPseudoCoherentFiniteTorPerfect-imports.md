# DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude

## Reason

Prune unused proof-plan imports and make proof-only FlatModel a private import.
Expose Projective and TorAmplitude explicitly because they occur in the unchanged signature.
Keep FlatResolution public because the signature needs its ModuleCat Grothendieck and
functorial-flat-resolution instances. No declaration signature or definition changes.
The public-import adjustment requires this record under stage 3 section 3.

## Old

```lean
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel
```

## New

```lean
public import Mathlib.Algebra.Module.Projective
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion
```

## Users

Read-only tools/downstream.py --uses found 376 downstream modules; only
PerfectAffineBoundedProjective mentions the unchanged theorem. Both direct importers
import this module privately. Their original source files were checked against the
revised compiled module in the scratch sandbox. Neither requires an adaptation, and
neither reexports this module's removed proof imports. All definitions and target meanings
are unchanged. The table records every downstream module and its locally recorded holder.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | T1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | H3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | J1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.NoetherianPerfectDirectImage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective | unclaimed | Direct private importer; original compiled against revised module; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectAffineClassesSmall | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectAffineFinitePresentation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | B3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | H1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel | B3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectIntoSupportPowerTorsion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension | unclaimed | Direct private importer; original compiled against revised module; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSummand | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PerfectThickClosure | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | Q1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | X3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | N2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | V1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | Y3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperPerfectDirectImagePerfect | F1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | N3 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | J2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | C2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.CategoryTheory.DerivedCategory.PerfectScalarExtension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| TargetsCheck | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | K2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged signature and definitions; private import boundaries preserve exported statements. |

## Status

landed 20261012T194147-L-467038 2026-10-12 (merge of deliver/U3/Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect)
