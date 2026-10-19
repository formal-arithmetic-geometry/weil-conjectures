# AlgebraicGeometry.Etale.isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts

## Reason

The retained proof closes the original theorem with private helper declarations for an
explicit finite-free resolution and countable telescope. Preflight classifies the added
`open`, `variable`, `universe` and scoped `omit` commands as a potential interface change.
This record documents their exact scope. All new declarations are private, and their local
namespace and section are closed before the original public theorem. The extra monoidal
namespace opening supplies notation only within this file. No instance, notation, attribute,
public declaration type, definition or public import is added or changed. The theorem's
signature is identical to the current shared source, including universes and visibility.

## Old

The original theorem signature was:

```lean
theorem isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    [PreservesColimitsOfShape (Discrete ℕ)
      (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]
    (K : DerivedCategoryModule A U) (N : ModuleCat.{u + 1} A) [Finite N] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)))
```

Its proof was `by sorry`. The file's nondeclaration commands indexed by the interface
checker were:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
```

## New

The theorem signature is unchanged, verbatim:

```lean
theorem isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    [PreservesColimitsOfShape (Discrete ℕ)
      (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]
    (K : DerivedCategoryModule A U) (N : ModuleCat.{u + 1} A) [Finite N] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)))
```

Its proof is complete with zero local holes. The checker now indexes these commands:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits
universe v
variable {R : Type v} [CommRing R]
variable {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] {F G : _root_.DerivedCategory (ModuleCat.{v} R) ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
omit [NatTrans.CommShift τ ℤ] in
```

The additional universe and variables occur inside `namespace ExceptionalConstantTensor`;
the functor variables and the `omit ... in` occur inside `section Devissage`. Both scopes end
before `namespace AlgebraicGeometry.Etale`. Only private helpers use them. The top-level
`open CategoryTheory.MonoidalCategory` affects name and notation resolution in this file;
it does not export an opening to importers. No downstream statement changes meaning and no
target review is reopened. The retained public import list is identical. All added or
removed imports are proof-only. The DAG change records the completed route and removes
obsolete tool-use approvals; its mathematical statement is unchanged.

## Users

`tools/downstream.py` lists 400 transitive importers. With `--uses` for the theorem,
only the item's own module mentions the declaration textually. Every transitive importer
is listed below, with current claim holders. Since the public signature and imports are
identical and all new helpers are private, each retains the same statement and meaning;
none requires adaptation. No module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ExceptionalConstantTensor | B7 | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude | R6 | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Same statement and meaning; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same statement and meaning; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same statement and meaning; no adaptation. |
| TargetsCheck | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same statement and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same statement and meaning; no adaptation. |

## Status

landed 20261019T002508-L-2141851 2026-10-19 (merge of deliver/B7/Sheaf.AlgebraicGeometry.ExceptionalConstantTensor)
