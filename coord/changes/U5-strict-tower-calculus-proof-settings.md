# AlgebraicGeometry.ProEtale.StrictTower: proof-local elaboration settings

## Reason

The stage-3 static preflight requires a change record for new section settings and
`attribute` commands. The new attributes are all explicitly `local`, and the new
section-level options end at the corresponding `end`. These commands prevent expensive
unfolding of the concrete sheaf and derived adjunctions while checking private proof
helpers. No public declaration, signature, definition body, instance, public import,
notation, or persistent reducibility attribute changes.

## Old

The existing file-wide settings are preserved verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
```

There were no `PullbackUnits`, `NormalizedIdentities`, or `GammaIdentities` proof sections.

## New

The following new section-level commands are scoped as shown (proved declarations
between them are omitted here):

```lean
section PullbackUnits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction moduleRComp moduleRId
attribute [local irreducible] moduleGComp
attribute [local irreducible] gComp gId towerGComp adj jAdj G R J alpha
end PullbackUnits

section NormalizedIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] gComp gId adj jAdj G R J alpha
end NormalizedIdentities

section GammaIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] adj jAdj G R J alpha gComp gId jId
end GammaIdentities
```

Individual private proofs also use declaration-scoped `set_option ... in` commands.
The three private data aliases (`moduleAdj`, `moduleGId`, `towerGId`) use `@[irreducible]`
and contain explicit constructions, with no postponed data. None is exposed in a public
signature or public definition. The existing namespace, variables, open commands and
file-wide options remain unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus --uses
pi_components beta_id gamma_identities` found 569 transitive importers. The only
external textual users of these three declarations are
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` and
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. Both use unchanged signatures.
For completeness the table lists every transitive importer; no consumer file is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | U5 | Private proof helpers and scoped elaboration settings only. |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | P4 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | D2 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | S3 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | U2 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.CategoryTheory.FilteredDerivedOperationLifts` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementShape` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementSquare` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportSiteCoherence` | U4 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProjectionActionLaws` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | M3 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperOpenTowerComparison` | H1 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RefinementExchangeCoherence` | H4 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementClopen` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementCoefficientSquare` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementConstruction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementCore` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.RingedRefinementFinite` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTensorUnit` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.SystemTensorMateArrows` | H8 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | S4 | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | None: signatures and exported settings unchanged; no adaptation. |

## Status

landed 20261020T211839-L-3510121 2026-10-20 (merge of deliver/U5/Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus)
