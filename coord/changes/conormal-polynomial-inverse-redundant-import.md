# ConormalPolynomialInverse redundant import

## Reason

Remove an unused direct public import. `Mathlib.RingTheory.Ideal.Cotangent`
already transitively publicly imports `Mathlib.RingTheory.Ideal.Quotient.Operations`.
A scratch compilation without the latter succeeds. The theorem statement,
all definitions, and the public declaration closure retain the same meanings.
No target needs semantic re-review and no downstream adaptation is required.
This record documents an import-only edit required by the stage-3 preflight.

## Old

```lean
public import Sheaf.RingTheory.EtalePolynomialCertificate
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
```

## New

```lean
public import Sheaf.RingTheory.EtalePolynomialCertificate
public import Mathlib.RingTheory.Ideal.Cotangent
```

## Users

Every transitive downstream module listed by `tools/downstream.py
Sheaf.RingTheory.ConormalPolynomialInverse --names` is listed below.
No file held by another group is changed. The only direct importer is
`Sheaf.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate`.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineEtaleDescentData` | H1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | B3 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | K2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | G1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.CofilteredEtaleLimitSections` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity` | H1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity` | K2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity` | N2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | S1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | T1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | V1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | U1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | N1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.DirectedEtaleLimitSections` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleAffineChartDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit` | B2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleComplexClassDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening` | E1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent` | W2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` | ORCHESTRA | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleLimitCohomologyClassDescent` | F1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing` | S1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleSetSectionEventualEquality` | C2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.EtaleSetSectionLift` | C2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleAlgebraStage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleFiniteTypeClosedFibreStage` | W3 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardSetStalkAux` | G2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer` | K2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | J2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberH0EtaleInjective` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberH0FiniteLift` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberH0FiniteSection` | B2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberH0ProjectionRestrictions` | B2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison` | C3 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity` | C3 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing` | A2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent` | A2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.IntegralPointedClopenRefinement` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.LimitPullbackSectionsColimit` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.NormalGenericConstant` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.NormalizedGenericDataCore` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts` | M2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange` | T1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | ORCHESTRA | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.PullbackSectionsIsColimit` | M3 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization` | Z2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso` | F2 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | F1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.EtaleFiniteDataDescent` | ORCHESTRA | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.FiniteHypercoverDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.FiniteHypercoverDescentParts` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.GabberCriterion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.GabberCriterionDegree` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.GabberPrincipalClassLocallyZero` | J1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.GaloisLisseRepresentations` | H1 | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `Sheaf.Paper.StrictHenselianZariskiEtaleComparison` | H2 | Unchanged; the same public declarations remain transitively available. |
| `TargetsCheck` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | A2 | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | C1 | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.AffineSpace` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Defs` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Inversion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Perverse` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Properties` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | S2 | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | J2 | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.Integral.Exact` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | none recorded | Unchanged; the same public declarations remain transitively available. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | none recorded | Unchanged; the same public declarations remain transitively available. |

## Status

landed 20261012T135301-L-1684305 2026-10-12 (merge of deliver/P2/Sheaf.RingTheory.ConormalPolynomialInverse)
