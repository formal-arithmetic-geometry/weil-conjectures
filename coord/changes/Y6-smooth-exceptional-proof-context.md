# AlgebraicGeometry.Etale.smooth_exceptional_base_change

## Reason

The completed proof uses private helpers generic in the coefficient category. Their
universe variables avoid an expensive specialization during kernel checking. Local
instance attributes select the existing canonical universe model for the small etale
site and the braiding induced by its symmetric structure, matching the upstream API.
The stage-3 command scanner requests this record for those commands. No exported
instance is introduced. Every existing public signature, definition body and public
import is unchanged. The four private proof imports do not re-export their declarations.
The target statements and their meanings are unchanged; no definition repair or consumer
adaptation is part of this delivery.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
```

## New

```lean
universe u u' w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Fix the canonical universe model before elaborating the derived functors.
attribute [local instance] Scheme.Etale.essentiallySmall

attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
```

The additional universe variables occur only in private helpers. Both attributes are
local to this module's namespace. Local smallness selects an existing proof of a Prop;
local braiding priority selects the same symmetric braiding as the upstream tensor
lemmas. The public definitions keep their original bodies verbatim.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange --uses
smoothExceptionalBaseChangeMap smoothDualizingBaseChangeMap smoothSquarePullbackIso
smoothDualityTensorBaseChangeIso smooth_exceptional_base_change` reports 349 downstream
modules. Textual users of the public declarations outside this module are
`Sheaf.Paper.AmbientDiagonalPurityBaseChange`,
`Sheaf.Paper.ExceptionalCoefficientComparison`, and
`Sheaf.SecSmoothPurity.PurityDncCoefficientTransport`. Their statements use the same
canonical maps and retain exactly the same meaning. All public definitions and theorem
signatures are unchanged; local attributes do not propagate to importers. No downstream
module is edited or needs adaptation, regardless of its claim holder. The table includes
every transitive importer; the group column is inapplicable because none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange | Y6 | Complete proof; private helpers and local elaboration context; public API unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityFiniteReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| TargetsCheck | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.Statement | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not queried (not adapted) | Public API and statement meaning unchanged; no adaptation. |

## Status

landed 20261019T034358-L-427047 2026-10-19 (merge of deliver/Y6/Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange)
