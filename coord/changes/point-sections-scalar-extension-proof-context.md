# Sheaf.Paper.PointSectionsScalarExtension proof context

## Reason

The stage-3 preflight requests a change record because it detects new `variable`, `open`,
namespace/section and local-attribute commands outside theorem bodies. These commands
support fully proved private helpers; this delivery does not change any existing
statement, public definition body, public import, instance priority or exported attribute.
All 14 original holes are proved. No definition repair or consumer adaptation is needed.

The generic tensor and localization helpers require additional universe variables.
`AlgebraicGeometry.Scheme` is opened for the point-cover calculation. Local irreducibility
keeps elaboration from expanding the chosen scalar-extension witness and its projections.
Four theorem-local unused-section-variable linter settings avoid a costly syntactic check
while retaining every original public signature. No elaboration limit is increased.

## Old

The existing header context was:

```lean
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
```

There were no private-helper sections or local irreducibility attributes. The final theorem
was in the original `Constructible` section with the original point/scalar variables in
scope. Its declaration signature is unchanged by this packet.

## New

The header context is:

```lean
universe u a b c r w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
```

The new local attributes, at the helper sections that need them, are:

```lean
attribute [local irreducible] completedScalarChangeData
attribute [local irreducible] completedOrdinaryScalarExtension integralOrdinaryScalar
```

Private helper sections bind their own categorical, ring and scalar variables:
`Transfer`, `GenericCoefficientSquare`, `PointScalarFunctorComparisons`,
`PointOrdinaryAssociator`, `GenericDerived` and `Tower`; `Tower` binds `universe x y z`.
These sections are closed before later public declarations. Additional namespaces contain
only private helpers, with variables for their displayed types. The final original theorem
is reopened in `Constructible` with:

```lean
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
```

Its text and elaborated parameters are preserved. Every earlier existing declaration's
header has also been compared with the source. Existing data definitions are verbatim;
all new helpers are private and proved. None of these proof-context choices propagates a
new interface to consumers, so no target meaning or second-stage statement review changes.

## Users

`tools/downstream.py Sheaf.Paper.PointSectionsScalarExtension --uses
pointSectionsScalarExtension pointCompletedSections pointSectionsTensor
pointOrdinaryDerivedComparison pointIntegralScalarUnit pointIntegralScalarAssoc
pointRationalSectionsScalarExtensionIso` reported 660 transitive consumers at inspection.
The table below includes the item and all current transitive consumers (including any
newly landed while the read-only inspection ran). Holders are snapshots of claim records.
No consumer changes: every original signature and public definition is retained, and
private imports/helper declarations do not become consumer API. Textual uses of the
inspected names occur in AdicLisseCohomologyCalculus, AdicSectionCanonicalModels,
FiniteCoefficientPoint, PointRealizationCoefficientComparison and PointSectionsTensorShift;
the same preservation argument applies to each of their exact uses.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.SupportLongExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No adaptation; interface preserved |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | No adaptation; interface preserved |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | No adaptation; interface preserved |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AmbientIndDerivedSums` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.AmbientIndDerivedTriangulated` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CartesianCoefficientTwists` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CartesianCoefficients` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ClosedSupportConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientHeart` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientHeartFiltration` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientHeartGeneration` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientHeartLisseExtensionConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientHeartSheafConeWitness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportReductionTower` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportReductionTowerConstruction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleCompactnessBounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleExtContinuity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleHomContinuityDevissage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DerivedGeometricStalk` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DetIndHeartIISums` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerLimit` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerSystem` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DirectImagesConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleProEtaleCoefficientTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldTwistInverse` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientPoint` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteTateSiteDescent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteWindow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FormalClosedSupport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FormalClosedSupportII` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FormalClosedSupportIILimits` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IdentificationFibreAdjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndConstructibleExtensions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndConstructibleFilteredColimits` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndHeartCanonicalPresentation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndHeartFullFaithfulness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndHeartIIVanishing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IndHeartKernelsCokernels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstructibleCompactness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralHeartLocalModel` | C2 | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralIndConstructibleHeartClosure` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralIndConstructibleStability` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralIndHeartRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralModelsOperations` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralStratumHomFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTwistBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTwistDerivedScalar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTwistDerivedScalarCanonical` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntegralWindowCoproductComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LisseIntegralCompletedRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PbcCohomologySheaves` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PbcQbarStandardCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PbcSupportCondition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorFiniteModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorQbar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorRational` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreDerivedTensorScalar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointFibreEquivalence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointSectionsReconstruction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PointSectionsScalarExtension` | G2 | 14 proofs; interface preserved |
| `Sheaf.Paper.PointSectionsTensorShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtaleTateTwists` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityConventions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityFiniteKummerLevel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QbarTwistCommonStage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SignedTwistReductionComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | Z7 | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.StratifiedLatticeRank` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedCupFunctoriality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedExteriorClasses` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TateTwistLocallyFree` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TopologicalStratifiedLisseLattices` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassChern` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceBaseChangeFirst` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TwConventions` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.TwistPreservesFiniteness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.VerdierExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | No adaptation; interface preserved |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ReductionDirectImageComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FieldTensor` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | No adaptation; interface preserved |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | unclaimed | No adaptation; interface preserved |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Targets.PoincareTateBoundedConstructible` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | No adaptation; interface preserved |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | No adaptation; interface preserved |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | No adaptation; interface preserved |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | No adaptation; interface preserved |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No adaptation; interface preserved |

## Status

landed 20261020T211716-L-3490895 2026-10-20 (merge of deliver/G2/Sheaf.Paper.PointSectionsScalarExtension)
