# Local elaboration attributes in FlatBaseChangeModuleLerayComparison

## Reason

Type comparison of the chart transport and edge equations otherwise unfolds the
resolution-based moduleCohomologyFMap and open restriction construction repeatedly,
exceeding the single-file compile limit. Keep these two maps named during this
file's proof. The local irreducibility attributes end with this namespace/file;
they do not change a definition, statement, or exported reducibility attribute.
Preflight classifies any new attribute command conservatively as an interface
command, so this record documents it. No target statement changes or target
semantic review is needed.

## Old

```lean
attribute [local instance] enoughInjectives
```

## New

```lean
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap cohomologyOpenRestriction
```

## Users

All modules returned by tools/downstream.py are listed below. The direct theorem
user is FlatBaseChangeTargetLerayComparison; the rest depend transitively on it.
Every signature stays identical, and local attributes have no downstream effect.
No modules besides the item and new statement modules are adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeAffineDictionary | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeAffineTarget | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison | U3 | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionAffineSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineData | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineModel | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineRestrictionIso | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineTransport | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonFlatTransportSquare | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFlatQuotientMateData | D2 | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotient | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsLocalStalkComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImageNoetherian | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct | D2 | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraLift | D2 | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No signature or definition change; no adaptation. |
| TargetsCheck | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature or definition change; no adaptation. |

## Status

landed 20261013T155944-L-1306402 2026-10-13 (merge of deliver/U3/Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison)
