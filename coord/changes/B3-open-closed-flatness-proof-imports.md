# AlgebraicGeometry.openClosedFlatness_etale and openClosedFlatness_proEtale

## Reason

Both theorem signatures are unchanged. Their proofs now use geometric fibers on the étale
site and fixed-scalar realization with kernel detection on the pro-étale site.
The previous public import of `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` is unused
and removed. The monoidal namespace is opened for proof notation. These header changes
trigger the public-interface review gate, although neither changes a declaration's meaning.

## Old

```lean
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

```

The namespace command was `open CategoryTheory CategoryTheory.Limits`.

## New

```lean
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.SixFunctors.ProEtaleIntrinsicTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses

```

The namespace command is `open CategoryTheory CategoryTheory.Limits MonoidalCategory`.
No definition or theorem statement changes; the two original `sorry` proofs are replaced.

## Users

`tools/downstream.py Sheaf.SixFunctors.OpenClosedFlatness --uses
openClosedFlatness_etale openClosedFlatness_proEtale` finds the following transitive importers.
Neither theorem name occurs in any consumer. The three direct imports are proof imports;
two already import ProEtaleRingedOpenClosed independently. The third uses étale declarations
and has no reference to the removed module's pro-étale declarations. Public imports of the
item needed by its theorem statements are retained. Thus none of these modules needs an
adaptation or has a changed statement. Opening a namespace in this module is lexical and
changes no imported declarations or downstream name resolution.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | X2 | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | D4 | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` | A9 | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` | G3 | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportQuotientFlat` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | No signature change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No signature change; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicClosedConstructible` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalBase` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalCoherence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalComposition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalOperations` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalProjection` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalProjectionData` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicExceptionalScalars` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | No signature change; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | K2 | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.BoundedConstructibleHomFiniteness` | H5 | No signature change; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | No signature change; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | E1 | No signature change; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | No signature change; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | No signature change; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | No signature change; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | T9 | No signature change; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | Z7 | No signature change; no adaptation. |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | S1 | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | No signature change; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalSystemAdjunction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | U3 | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | No signature change; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteTorInternalHomAnyField` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | H2 | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | B4 | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | F5 | No signature change; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | No signature change; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | No signature change; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | J5 | No signature change; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | No signature change; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | D7 | No signature change; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | No signature change; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | No signature change; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | E9 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | P2 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | K5 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | Q3 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | K6 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | U2 | No signature change; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | F8 | No signature change; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDivisorClass` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDncComparisons` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | K8 | No signature change; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | No signature change; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | No signature change; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | R3 | No signature change; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SfPreservationClass` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | X7 | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothExceptionalBaseChangeStatement` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothMateCounitCancellation` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | S6 | No signature change; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TensorTraceTranspose` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | No signature change; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TraceTransposeBaseChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | K3 | No signature change; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | C3 | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | F3 | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | H6 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.EtaleInternalHomDevissage` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FiniteCompactProetale` | A2 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FlatModel` | A3 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FlatModelGeneration` | S3 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | E3 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | M7 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | N4 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | G9 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | B4 | No signature change; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | No signature change; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | U1 | No signature change; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | No signature change; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | No signature change; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | No signature change; no adaptation. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | unclaimed | No signature change; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | No signature change; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No signature change; no adaptation. |
| `TargetsCheck` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.Finiteness` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No signature change; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No signature change; no adaptation. |

## Status

landed 20261019T002505-L-2141220 2026-10-19 (merge of deliver/B3/Sheaf.SixFunctors.OpenClosedFlatness)
