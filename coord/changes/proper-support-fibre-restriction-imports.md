# ProperSupportFibreRestrictionCompatibility import interface

## Reason

The proof works directly with ModuleCat-valued inverse images and their composition-unit
coherence. The former reductions to abelian and set sheaves are unused. Remove their direct
imports and add only the three proof dependencies actually used. The theorem's signature and
its docstring are unchanged. All new helpers and constructions are private. All irreducibility
attributes are local; no public definition has changed. This record also covers the additional
local open/attribute commands flagged by the static interface checker.

## Old

```lean
public import Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap
public import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap
public import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.ProperSupportSectionLocality
import Sheaf.AlgebraicGeometry.EtaleModuleSectionClosedSupport
```

## Users

The source scan's transitive importers are listed below. No importer is edited or has its
statement changed. Holder ownership is immaterial to this delivery because no forced adaptation
is performed. The shared snapshot's direct importer is
`Sheaf.AlgebraicGeometry.ProperSupportExchangeRange`; server preflight additionally identifies
`Sheaf.SecSmoothPurity.ProperSupport` in its newer delivery base. The delivery preflight checks
the consumers against that base. The exact original theorem signature is retained, so no caller
of the theorem requires adaptation. Removed public imports expose only unused auxiliary theory;
the required statement types remain supplied by the two retained public imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | claimed | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | claimed | no declaration change; not adapted |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.FiniteCompactSupportFibreSupportBound | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.A1QbarOpenClosedCohomology | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicHeartIntrinsicFibres | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicLocalCharacteristicFactor | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicMiddleExtensionConstructible | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicPunctualWeights | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicPurityFiniteTensor | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicPurityObjects | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicPurityRootComparisons | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicPuritySourceReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicPurityTwistReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdicSectionClosedSupport | claimed | no declaration change; not adapted |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AdmissibleVerdierExchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.AffineCurveHcZero | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AffineLineInvariance | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.AmplificationProper | claimed | no declaration change; not adapted |
| Sheaf.Paper.ArithmeticRoots | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BasicOperationsCoefficientReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.BoundaryDualizingComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.BoundaryQFoundation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BoundaryQMaps | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BoundaryQTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.BrownExceptionalAdjoint | claimed | no declaration change; not adapted |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.CartierClassAgreement | claimed | no declaration change; not adapted |
| Sheaf.Paper.ChernFlagFormula | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CoefTowerCoaugmentation | claimed | no declaration change; not adapted |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CoefficientTowerShriekCalculus | claimed | no declaration change; not adapted |
| Sheaf.Paper.CohomologicalSmoothComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | claimed | no declaration change; not adapted |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | claimed | no declaration change; not adapted |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonAdicSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | claimed | no declaration change; not adapted |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CommonStageWeilShriek | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactFiberStalk | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportCondensedRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportFiniteAction | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportPerfectness | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportProjectionFormula | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportSiteCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactificationCoherenceCocycle | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactificationLocalizing | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CompactificationRefinementLocalizing | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompleteCompactSupportProetale | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompletedOperationTowerSubstitution | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompletedPullbackTensorComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompletedTensorHomTranspose | claimed | no declaration change; not adapted |
| Sheaf.Paper.CompositeIntegrationCounit | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConnectedConstantH0 | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstantWeilStructure | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleCompleteBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleHomComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleProjectionMates | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructiblePullbackTExact | claimed | no declaration change; not adapted |
| Sheaf.Paper.ConstructibleTruncations | claimed | no declaration change; not adapted |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | claimed | no declaration change; not adapted |
| Sheaf.Paper.ContinuousRationalDerivedRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CtfHomConditionB | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | claimed | no declaration change; not adapted |
| Sheaf.Paper.DeltaProperPushforward | claimed | no declaration change; not adapted |
| Sheaf.Paper.DeltaRestriction | claimed | no declaration change; not adapted |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | claimed | no declaration change; not adapted |
| Sheaf.Paper.DerivedPullbackTensorIso | claimed | no declaration change; not adapted |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DirectImagesConstructible | claimed | no declaration change; not adapted |
| Sheaf.Paper.DlConstantFieldCharts | claimed | no declaration change; not adapted |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DualBaseChange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DualStalkFrobenius | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.DualizingObjectPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | claimed | no declaration change; not adapted |
| Sheaf.Paper.EtaleCompactScalarCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | claimed | no declaration change; not adapted |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalCoefficientComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalFiniteRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalInverseImageExistence | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalProEtaleRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ExchangeFunctoriality | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExplicitExceptionalPreservation | claimed | no declaration change; not adapted |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FieldShriekCompositionQcqs | claimed | no declaration change; not adapted |
| Sheaf.Paper.FieldShriekLowerBound | claimed | no declaration change; not adapted |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FieldTorAmplitude | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FieldWeilShriekShiftData | claimed | no declaration change; not adapted |
| Sheaf.Paper.FilteredCoefficientTensorBounds | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteClosedShriek | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientHomChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteConstructibleHom | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteDncNormalizationReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteEtaleDescent | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteExtensionProperBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteExtensionReductionConeBound | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteForwardProductSymmetry | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteFreeCoefficientExtension | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteFreeProjectionExchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | claimed | no declaration change; not adapted |
| Sheaf.Paper.FinitePointInternalHomEvaluation | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteProductCompactification | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteProjectionActionLaws | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteProperLocalizing | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteReductionAffineOrientation | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteReductionChartCalculus | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteReductionComparisons | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteReductionRootCharts | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteRingSectionDeformation | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothGammaNormalization | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothPullbackExchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteStageVerdierBiduality | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteStructuralMapsCommShift | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteSystemPullbackCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.FiniteTorStability | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FixedStalkIdentificationReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.FlagLocalComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FlagPullbackInjective | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FourierKernelConvolution | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FourierTraceFormula | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FourierTraceFunctions | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | claimed | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusExchangeEquivalence | claimed | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | claimed | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GeometricFiberQbar | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.GlobalVerdierDuality | claimed | no declaration change; not adapted |
| Sheaf.Paper.HomFiniteProjective | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IntegralCoherenceTower | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IntegralComparisonSequenceSystems | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralConstructibleInternalHom | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralConstructibleReductionFibres | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralDirectImageTower | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralExceptionalInverseImage | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralOpenImageProperFormulas | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralPointTransportTowerPowers | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralPointTransportTowerRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralProperBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralProperDirectSums | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralProperProjectionFormula | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralPullbackComparisonRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralPullbackComposition | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralPullbackResolutionMatching | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IntegralTowerInverseImageUnit | claimed | no declaration change; not adapted |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.InterchangeProperPasting | claimed | no declaration change; not adapted |
| Sheaf.Paper.InternalAdjunctionPairingChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.InternalHomPullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | claimed | no declaration change; not adapted |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.IteratedWeilCocycle | claimed | no declaration change; not adapted |
| Sheaf.Paper.IteratedWeilMap | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LisseExtensionInertia | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalFrobeniusTrace | claimed | no declaration change; not adapted |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | claimed | no declaration change; not adapted |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalizedTopChern | claimed | no declaration change; not adapted |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.MateOpenRestriction | claimed | no declaration change; not adapted |
| Sheaf.Paper.MiddleExtensionHcZero | claimed | no declaration change; not adapted |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | claimed | no declaration change; not adapted |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.OpenCompactSupportFiniteTor | claimed | no declaration change; not adapted |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PfRefinementCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PointCompletedEvaluation | claimed | no declaration change; not adapted |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PreservationConstructible | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProEtaleProperOpenInterchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProjectionFiniteReduction | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperBaseChangeRational | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperCoincidenceFrobenius | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperCompactCoincidence | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperHeartBound | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperOpenCoefficientMate | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperOpenCoefficientRefinement | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperOpenTowerComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperProductCounitTranspose | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperSectionsSemilinearGerms | claimed | no declaration change; not adapted |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PunctualSpectrumExactFibre | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurAdicReconstruction | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityAffineLineOrientation | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityChernClasses | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityCoprojection | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityDiagonalDualizingObject | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityDiagonalSectionPasting | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityDivisorClass | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityFrameIndependence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.PurityGeneralAdmissibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityGysinStructure | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityRelativeKummer | claimed | no declaration change; not adapted |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | claimed | no declaration change; not adapted |
| Sheaf.Paper.PuritySourceTransports | claimed | no declaration change; not adapted |
| Sheaf.Paper.PurityTwistCancellation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.QbarCompactSupportBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.QbarProperBaseChange | claimed | no declaration change; not adapted |
| Sheaf.Paper.QcqsCompactSupportRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalCoefficientCategoryComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalDirectImageRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RationalLocalizingProjectionFormula | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalPurityPresentation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RationalScalarTransposeCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalSmoothPurityCanonical | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalStalkExact | claimed | no declaration change; not adapted |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RefinementExchangeCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RegularImmersionClassData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RegularImmersionPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RelativeSupportBottomDescent | claimed | no declaration change; not adapted |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RestrictionLocal | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.RingedRefinementCoefficientSquare | claimed | no declaration change; not adapted |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ScalarExtensionTowerCoherence | claimed | no declaration change; not adapted |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | claimed | no declaration change; not adapted |
| Sheaf.Paper.SfBidualityClass | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SfCommonStageDirectImage | claimed | no declaration change; not adapted |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | claimed | no declaration change; not adapted |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | claimed | no declaration change; not adapted |
| Sheaf.Paper.SfProEtaleProjectionFormula | claimed | no declaration change; not adapted |
| Sheaf.Paper.SiteComparisonEdgeSection | claimed | no declaration change; not adapted |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SixFunctorDatum | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityMap | claimed | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityQbar | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityTowerBound | claimed | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | claimed | no declaration change; not adapted |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | claimed | no declaration change; not adapted |
| Sheaf.Paper.SmoothTrace | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | claimed | no declaration change; not adapted |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.SystemClopenTensorCompatibility | claimed | no declaration change; not adapted |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | claimed | no declaration change; not adapted |
| Sheaf.Paper.SystemOperationExchangeRealization | claimed | no declaration change; not adapted |
| Sheaf.Paper.SystemTensorMateArrows | claimed | no declaration change; not adapted |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TensorAdjunctionExchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.TowerClassChern | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassCoefficients | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassDiagonal | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassFinite | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassProjective | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassPullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassReduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassSystems | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerClassTwisting | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | claimed | no declaration change; not adapted |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFixedScheme | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TrfDevissageGeneration | claimed | no declaration change; not adapted |
| Sheaf.Paper.TrfWitnessedOpenPullback | claimed | no declaration change; not adapted |
| Sheaf.Paper.TwConventions | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TwFrobeniusAction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.TwistFrobeniusScalar | claimed | no declaration change; not adapted |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.UnboundedProperOpenInterchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.VaryingRingGraphSummand | claimed | no declaration change; not adapted |
| Sheaf.Paper.VectorBundlePurity | claimed | no declaration change; not adapted |
| Sheaf.Paper.VectorBundleThomClass | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.VerdierExchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilCompactSupportCohomology | claimed | no declaration change; not adapted |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilFourierInversion | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilIndSheafCategory | claimed | no declaration change; not adapted |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WeilPullbackLocalFrobenius | claimed | no declaration change; not adapted |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.WfTensorCompletionFrobenius | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlFiniteAdicDirectImage | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlFrameworkOpenExchange | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | claimed | no declaration change; not adapted |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Paper.ZlShriekComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.MixedBaseChange | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ProperSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ReductionDirectImage | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.ReductionExceptional | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | claimed | no declaration change; not adapted |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.AmbientProperOpenPasting | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.BoundaryDualityDischarge | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefQbarVerdier | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefTowerTraceRectification | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CompactCoefficientComposition | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.CompositionProjectionMate | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.CtfStabilityDirectImages | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteDualizing | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteExceptional | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FiniteMappingAdjunction | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FrobeniusFixedPoints | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FrobeniusPointTransport | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.GeneratorReductionStatement | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralBasicOperationShift | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralDualizing | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralOperationShiftData | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRealizationRecursion | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.IntegralVerdier | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.OpenAdjunctionShift | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.OpenFactorCoherence | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.ProperImageLocalizingProper | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.ProperOpenProjectionMate | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.RationalOperations | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.RationalRetractEvaluation | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.RationalVerdier | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | claimed | no declaration change; not adapted |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | claimed | no declaration change; not adapted |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | claimed | no declaration change; not adapted |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Targets.PoincareUncurry | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Targets.SmoothPurityQbar | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.Targets.VectorBundlePurity | claimed | no declaration change; not adapted |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | claimed | no declaration change; not adapted |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.TraceFormula.PointTransportComposition | claimed | no declaration change; not adapted |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed (shared snapshot) | no declaration change; not adapted |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | claimed | no declaration change; not adapted |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | claimed | no declaration change; not adapted |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed (shared snapshot) | no declaration change; not adapted |
| TargetsCheck | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.PoincareDuality.Poincare | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.PoincareDuality.Verdier | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.SmoothPurity.Defs | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.Statement | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Basic | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.TraceFormula.Statement | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.Curve | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LFunction | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.Examples | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.Rationality | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed (shared snapshot) | no declaration change; not adapted |
| WeilConjectures.ZetaFunction.Weights | unclaimed (shared snapshot) | no declaration change; not adapted |

## Status

landed 20261020T131231-L-1264012 2026-10-20 (merge of deliver/X3/Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility)
