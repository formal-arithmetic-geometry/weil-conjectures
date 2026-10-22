# Sheaf.Paper.SbcCompletedOperations

## Reason

The stage-3 preflight requests a change record for added module commands, even when
all public declaration signatures and definition bodies are preserved. This record
covers proof elaboration controls, local reducibility/instance attributes and the
private-helper section introduced while closing the fifteen original proof holes.

The controls prevent large derived-category presentations from being unfolded during
categorical abstraction. The complete item compiles cleanly in 42.1 seconds under the
normal 60-second file limit. There is no statement or definition repair.

## Old

The original module-level elaboration/open commands were, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u r v w v' w'
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
```

None of the added commands listed below was present. Every original command remains.
All 74 original declaration signatures, all 51 original non-theorem bodies and all
six public imports are unchanged. No target declaration is edited.

## New

Added commands, in source order (repeated scoped options belong to different private
proofs):

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] sbcOrdinaryComp
attribute [local irreducible] smallModulesEquiv completedCechModulesEquiv
section CompletionPresentation
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
end CompletionPresentation
attribute [local irreducible] sbcCoefficientIso sbcFiniteCoefficientIso
attribute [local irreducible] sbcOrdinaryTheta sbcFiniteTheta sbcTheta sbcAdjunction
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency true in
```

Every added attribute is explicitly `local`. The additional variables are confined
to `section CompletionPresentation` and its private proved helpers. Scoped options
end with their following declaration; file-level options govern only this module's
elaboration. None of these commands installs an exported instance or changes the
reducibility of a declaration for importers. The public data constructions and their
normalizing equations remain the original ones.

## Users

Read-only `tools/downstream.py Sheaf.Paper.SbcCompletedOperations --uses ...` reports
307 transitive consumers. Its name searches for the affected SBC declarations find
external uses in `AdicSmoothBaseChange`, `ECoefficientSmoothBaseChange`,
`FiniteStageRationalExchangeData`, `QbarCoefficientSmoothBaseChange`,
`RationalOperationCoherence`, `RationalRawOperationCoherence`,
`RationalRawSquareExchangeCoherence` and `RationalSquareExchangeCoherence` (all under
`Sheaf.Paper`). Their uses retain the same functors, comparison morphisms, types and
reduction equation. Source inspection finds no required adaptation: original public
headers and data bodies are preserved, and the added commands are module-local.
This is an API/source audit, not a claim to have compiled all 307 consumers here.
Only the maintainer performs the global build.

The table includes every transitive consumer from that invocation, plus the item.
Holders are the claim-record snapshot at preparation; `unclaimed` means no claim
record was present. Every consumer has the same outcome: its statements keep their
meaning and no source edit is required.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicFiniteExchangeEncoding` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicNormalizedFibreData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicSmoothBaseChange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AdicStratifiedPullbackInterface` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AmbientCompleteRawSystem` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CanonicalOpenRestrictionModel` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CondensedERealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FinitePullbackStrictTowerComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteStageKaroubiExtension` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteStageRationalExchangeCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteStageRationalExchangeData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusFixedPairComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralPullbackShiftCoordinates` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralPullbackStrictRoosNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntrinsicConstructibleFibreExactness` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IntrinsicLocalLatticeComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.NormalizedHeartRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.NormalizedLatticeFiniteFree` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OpenRestrictionCompleteness` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.OrdinaryPullbackStratifiedModels` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PbcConstructibleReductionPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PbcQbarCompletedPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PerAdicNormalizedFibreComparisons` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | E9 | Unchanged API; no adaptation |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | M8 | Unchanged API; no adaptation |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalOperationCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalRawOperationCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalRawSquareExchangeCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalSquareExchangeCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealWeights` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationAdjointComparisons` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationCoefficientSquare` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationCompletedImage` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationCompletedPull` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationCompletedPullData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationLocalizedPush` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationPullOrdinarySystem` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.RealizationPullRationalDescent` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SbcCompletedOperations` | M9 | Proofs completed; public signatures and data preserved |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | P8 | Unchanged API; no adaptation |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfCompletedPullbackMateFactorization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfExactPullbackCounitNormalization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TrfDevissageGeneration` | C3 | Unchanged API; no adaptation |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TwConventions` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilGenericLissity` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Unchanged API; no adaptation |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Unchanged API; no adaptation |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unchanged API; no adaptation |

## Status

landed 20261022T011904-L-3229687 2026-10-22 (merge of deliver/M9/Sheaf.Paper.SbcCompletedOperations)
