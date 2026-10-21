# WeilConjectures.completedScalarChainComparison_existsUnique

## Reason

The construction proofs require explicit control of instance search and reducibility:
several integral-operations aliases give competing presentations of sheafification,
site size, and the standard derived category. The packet disables the duplicate aliases
while checking this module, uses local irreducibility to avoid expanding the chosen
change-of-rings witness and limits, and opens Preadditive for the cone calculation.
The generic private helpers bind two additional universe names. The static gate treats
these command changes as an interface change. No existing declaration type,
public import, or data-definition body changes; the instance-attribute changes are
listed explicitly below.
This record submits all such commands to the independent reader.

## Old

The original commands before the namespace, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
```

There were no later local reducibility commands or scoped transparency/heartbeat
settings in the original module, except the existing linter setting.

## New

The delivered commands before the namespace, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

attribute [local irreducible] HasDerivedCategory.standard

universe t u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped ChangeOfRings
```

The remaining added attribute commands, in their order in the file, are:

```lean
attribute [local irreducible] limit
attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness
attribute [local semireducible] limit
attribute [local irreducible] limit
```

Proof sections also select the two backward transparency settings explicitly. The
identity-unit theorem has a scoped 600000-heartbeat elaboration allowance; it still
uses the unchanged 60-second single-file compile limit. All helpers are private and
proved. Three original theorem bodies are replaced with proofs. The public theorem
statements, all public definition bodies, their docstrings, and all four public
imports stay verbatim. Proof imports are private and are listed in report.md.

## Users

The following is the complete transitive consumer list from tools/downstream.py.
Every published declaration used by these modules retains its signature, visibility,
and data definition. No consumer source changes are needed. The module-system public
imports are preserved; the independent reader and global build verify the resulting
instance environment. Current claim holders are recorded for information; none of
their modules is adapted in this delivery.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerNaturality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | B7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FrobeniusFactorization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary` | K9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonSectionModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportLongExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | D9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedFullSupportProduct` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicConstructibilityPredicateComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicHeartPullbackFibres` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | B9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AffineCoordinateSupportStalkContinuity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AmbTateRootProjectionReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AmbientIndDerivedSums` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.AmbientIndDerivedTriangulated` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryComparisonCompositionTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalOpenRestrictionModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CartesianCoefficientTwists` | P2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CartesianCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ClopenRoosIntegralDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeart` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartFiltration` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartGeneration` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartLisseExtensionConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartSheafConeWitness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTwistsDetailed` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CofinalFiniteReductionConstructibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageLisse` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageLocallyFree` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonTensorComparisonDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CommonTensorComparisonRepresentatives` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportArrowScalarTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportReductionTower` | C4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportReductionTowerConstruction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | B7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | F6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedExchangeCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedIntegralScalarData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedLineComplete` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedLineDerived` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedLineTensorCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | F5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedScalarChainShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedScalarShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedScalarUnitAdjunction` | A9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConcentratedSupportEtaleTransfer` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CondensedBoundedHomContinuity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CondensedERealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantWeilStructure` | F2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactnessBounded` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExtContinuity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleHomContinuityDevissage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | F7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenFiniteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenScalarComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoordinateGermCohomologyClasses` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoordinateGermConcentrationData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedGeometricStalk` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedOpenSquareRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DetIndHeartIISums` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerLimit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerSystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImagesConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | F1 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients` | X2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleIsoDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdIntegralIdentityRationalEquivalence` | R6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldTwistInverse` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | R7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientInputModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientPoint` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | Y6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | A4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | Y7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | Y8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteLocalModelRHomContinuity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteOpenProductSwap` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProjectionActionLaws` | G2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperProductTranspose` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | N1 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSiteCounitProjectionTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTateSiteDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTypeCoordinateSupportOrientation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupportII` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupportIILimits` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FourierAdicArtinSchreier` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FourierAdicCharacterOf` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | B3 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusFixedPairComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | A5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IdentificationFibreAdjunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IdentityOpenDerivedRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IdentityOpenUnderivedSquareNormalization` | H2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndConstructibleExtensions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndConstructibleFilteredColimits` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartCanonicalPresentation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartFullFaithfulness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartIIVanishing` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartKernelsCokernels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralAmbientCoefficientPresentation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralAmbientDirectImageEncoding` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralAmbientTowerComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | K5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleCompactness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleCompletionBridge` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralGeneralLfpHomInversion` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralIndConstructibleHeartClosure` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralIndConstructibleStability` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralIndHeartRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralIndLowerTail` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | G3 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineDerivedComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLinePowerComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineReductionDefinitions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineReductionRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineRestrictions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineTensorCompleteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModelsOperations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | A5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackShiftCoordinates` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackStrictRoosNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralQuotientCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralQuotientDirectImageComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralQuotientExchangeComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralQuotientProjectionComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralQuotientProjectionMap` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | K6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorComparisonSystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | G4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistBaseChange` | J4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalar` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalarCanonical` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralWindowCoproductComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwists` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicQbarCategory` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.InverseImagePullbackComparisonDerived` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | E9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarAugmentationCone` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarTensorKFlatModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LatticeSubquotientFiltration` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LatticeSupportedHomFiniteComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseIntegralCompletedRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | H1 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizedDirectImageComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.LocallyClosedRelativeTransposeNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.MixedWeightsStability` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedOpenRefinementCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | U4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OpenRestrictionCompleteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | K9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryPullbackStratifiedModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PartialKummerBoundaryUnitModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcCohomologySheaves` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcDescentFunctors` | J5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcQbarCompletedPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcQbarStandardCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PbcSupportCondition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PerAdicCommonStageTruncations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointAutomorphismRestrictionNatural` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointDerivedSectionsTensorDescent` | Q3 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointDerivedTensorTowerCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointExactDerivedModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorFiniteModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorQbar` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorRational` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorScalar` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreEquivalence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFieldTensorDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFiniteFreeSectionsTensor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointFiniteTensorComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointIntegralCompletedTensorComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointIntegralPerfectRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointIntegralSectionsConservative` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointQbarFibreShiftDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointRationalFibreExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointRationalSectionsHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointRationalSectionsLattice` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsReconstruction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsScalarExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsTensorShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleTateTwists` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | E9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | M1 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineChartExceptionalIdentification` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityConventions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFiniteKummerLevel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | G6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | M8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QbarIdempotentComplete` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QbarTwistCommonStage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QlbarDirectImageComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QlbarInternalHomCoefficientComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.QuotientSystemMixedCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizedHom` | C3 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocallyFree` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationFiniteConeModels` | S8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | J8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RationalTensorComparisonSystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealWeights` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealWeilSheaves` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealizationAdjointComparisons` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealizationCompletedPull` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealizationCompletedPullData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealizationPullOrdinarySystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RealizationPullRationalDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ResidueControlledFiniteHoms` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RoosIntrinsicUnitComparison` | H6 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.RootTowerLisseMorphismExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarCompletionAssociator` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExtensionExactIntrinsic` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTensorUnit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarModelImmersionExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | P8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfCompletedPullbackMateFactorization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfConstructibleHeart` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfExactPullbackCounitNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralConstructibleLinear` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralConstructibleTriangulated` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalBoundedConeTorsion` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalizationKaroubi` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfScalarExtensionComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SfWeilSheafComplex` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SignedLineTensorEquivalence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SignedTateCoefficientExponentNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SignedTwistReductionComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectComplex` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | Z7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SpecifiedHomScalarEvaluation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.StratifiedConstantModelProductBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.StratifiedLatticeRank` | D2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.StratifiedTorIntervalDevissage` | S3 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.StrictQuotientExpressions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCupFunctoriality` | P5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClasses` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedHomCocycleNormalization` | H5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedLatticeHomReductionTower` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TameRootTowerExtension` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistLocallyFree` | V7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TensorComparisonLocalizationDescent` | S9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TopologicalStratifiedLisseLattices` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeFirst` | V9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.TwistPreservesFiniteness` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilComplexQbarIdempotentComplete` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilGenericLissity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilInternalHomWeil` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WfTateTwist` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WfTateTwistCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle` | E2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle` | E4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImageComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | A2 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.WeilTwistRationalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityInput` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | R7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FieldTensor` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | Z9 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | M5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | W4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | T5 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeFrobenius` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Targets.PoincareTateBoundedConstructible` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | K4 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | H7 | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.ScalarModelAssociativity` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.TraceFormula.ScalarModelUnit` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Existing signatures and data constructions unchanged; no adaptation. |

No target declaration or definition used by a target changes meaning. Two original
named theorem holes remain; no new hole is introduced.

## Status

landed 20261021T214801-L-1854670 2026-10-21 (merge of deliver/H7/Sheaf.Paper.FiniteFreeCompletedScalarComparison)
