# DualizableEvaluationCriterion imports

## Reason

Remove a redundant direct public import. The retained module
`Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction` publicly imports
`Sheaf.AlgebraicGeometry.DerivedTensorStructure`, so the same declarations and instances
remain publicly visible through the same transitive closure. No theorem or definition
signature, visibility, or mathematical meaning changes. No target statement needs renewed
semantic review, and no downstream proof needs adaptation.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
```

## New

```lean
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion --uses
 dualizable_evaluation_criterion` lists 362 downstream modules in this local snapshot.
Only `Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison` directly imports this module
and mentions its criterion. All downstream modules retain exactly the same public import
closure, since the removed edge is duplicated by the retained public two-edge path.
The claim snapshot is local; no other group's files are changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | T1 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | G3 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | D2 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | N2 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | V1 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | C2 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| TargetsCheck | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Defs | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Inversion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Perverse | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Properties | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed (local claim snapshot) | No effect: identical public transitive imports and unchanged declarations. |

## Status

landed 20261012T194140-L-464780 2026-10-12 (merge of deliver/S3/Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion)
