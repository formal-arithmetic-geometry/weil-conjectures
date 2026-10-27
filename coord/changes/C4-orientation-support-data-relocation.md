# OrientationSupportData and its support pullback maps

## Reason

Delivery path: `coord/changes/C4-orientation-support-data-relocation.md`.
The returned head `5b85642a3aa` passed mathematical review, but the landing attempted
to apply this record by its basename. Reviewer corrections to this record must use
the full delivery path above. The record is retained in this repair packet, and its
consumer list and recorded claim holders are refreshed against current sheaf-dag.

Two independent remaining comparison steps must refer to the existing normalized support
chart without importing the orientation theorem that uses those steps. Move the four
existing declarations into `Sheaf.Paper.PurityAffineLineOrientationData` and publicly
re-export that module from `Sheaf.Paper.PurityAffineLineOrientation`. This is an interface
relocation with a shared implementation for the coefficient pullback wrapper, with no mathematical
definition or signature change. The original five public
imports of the orientation module are retained verbatim. No source-library file changes.
The chart and coordinateBoundary definitions are copied byte for byte, including their
docstrings. The coefficient pullback wrapper now calls the already published equivalent map; the
restriction map is verbatim. All
original declaration signatures were compared using the project declaration reader.

## Old

The following declarations were in `Sheaf.Paper.PurityAffineLineOrientation`:

```lean
/-- The canonical support chart of lem-pur-gysin-structure together with the actual
snake boundary. The formulas fix both the identification and its sign; none of the
maps is an unconstrained support isomorphism.
Source: blueprint main-20261015, Gysin identification and orientation construction
(blueprint: thm-pur-affine-line-orientation). -/
structure OrientationSupportData (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) where
  comparison : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
  openCoefficient : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
    (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true
  openCoefficient_spec : openCoefficient.hom = P.gysinOpenCoefficient h Y
  edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
    (localClasses P Y 2).obj (P.gysinClosed h Y)
  edge_spec : edge.hom = (comparison.edge 2).app (P.gysinClosed h Y)
  support : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y
  support_spec : support.hom = (globalSectionsFunctor (Modules P) Y).map
      (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
      edge.inv ≫ (comparison.supportIso 2).hom.app (P.gysinEtaleInput h Y)
  boundary : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤
  boundary_exact : Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤ boundary
  boundary_normalized : supportBoundaryNormalization (Scheme.ProEt.topology (Line Y))
    P.Coefficient (supportRestrictionArrow (zeroSection Y)) boundary

/-- The actual supported coordinate boundary in the published Gysin chart.
Source: blueprint orientation construction, pur_s sends 1 to the boundary of kappa(t)
(blueprint: thm-pur-affine-line-orientation). -/
def OrientationSupportData.coordinateBoundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    (D : OrientationSupportData P h Y) (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.gysinSupport h Y :=
  (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩
    (P.gysinKummerSection h Y a D.comparison D.openCoefficient)

/-- Canonical inverse image of the affine-line coefficient complex, through comparison
and the scalar-extended root pullback. This is defined for arbitrary base morphisms.
Source: blueprint affine-line datum and geometric-fibre paragraph
(blueprint: thm-pur-affine-line-orientation). -/
def orientationInputPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y) :
    (upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)).mapDerivedCategoryPlus.obj
      (P.gysinInput h Y) ⟶ P.gysinInput h T :=
  (supportHomDerivedComparison P (AffineSpace.map (ULift.{u} (Fin 1)) f)).inv.app
      (P.gysinEtaleInput h Y) ≫
    (nuPlus P (Line T)).map
      ((Functor.mapDerivedCategoryPlusSingleFunctor
          (Etale.upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)) 0).hom.app
          (P.twistEtale h (Line Y)) ≫
        (DerivedCategory.Plus.singleFunctor (EtSheaves P (Line T)) 0).map
          (P.twistEtalePullback h (AffineSpace.map (ULift.{u} (Fin 1)) f)))

/-- Pullback on the actual supported cohomology, with the canonical coefficient map.
The transport's supportUnit_spec fixes the underived kernel map by its inclusion;
derivedMap is its published right-derived base-change map.
Source: Milne, Section 9; blueprint orientation proof, restriction to a geometric point
(blueprint: thm-pur-affine-line-orientation). -/
def orientationSupportRestriction (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.gysinSupport h Y ⟶ P.gysinSupport h T :=
  (DerivedCategory.Plus.homologyFunctor (Modules P) 2).map
      ((p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback
        (AffineSpace.map (ULift.{u} (Fin 1)) f))).app (P.gysinInput h Y)) ≫
    (Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology (Line T)) (Modules P)
      (supportRestrictionArrow (zeroSection T)) 2).map (P.orientationInputPullback h f)

```

## New

The chart, coordinateBoundary and orientationSupportRestriction declarations in `## Old`
occur verbatim, with the same namespace, universes, visibility, names, types, fields and
bodies, in `Sheaf.Paper.PurityAffineLineOrientationData`. The signature of
orientationInputPullback remains verbatim; its implementation now uses the existing shared
coefficient map:

```lean
def orientationInputPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y) :
    (upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)).mapDerivedCategoryPlus.obj
      (P.gysinInput h Y) ⟶ P.gysinInput h T :=
  P.coordinateProCoefficientPullback h (coordinateLineMap f)
```

Unfolding `coordinateProCoefficientPullback`, `coordinateEtaleCoefficientPullback` and
`coordinateLineMap` gives the old orientationInputPullback body in the same order; the
equality is definitional (the worker's claim; a direct `rfl` check exceeds the 60 s compile
limit, so it was not re-verified by the reviewer). No module other than this one unfolds
orientationInputPullback. Reusing the published term avoids a repeated kernel conversion
of the large right-derived base-change maps in the coordinate-pullback assembly.

Reviewer correction (2026-10-25): the delivery had also rewritten the body of
orientationSupportRestriction as `p.coefficientGroupMap … (P.orientationInputPullback h f) 2`.
That broke `Sheaf.Paper.PurityAffineLineOrientationInjectivity` (unclaimed), whose private
lemma `orientationSupportRestriction_transport_eq` runs
`unfold orientationSupportRestriction SupportHomPair.Transport.derivedMap` and fails with
"Tactic `unfold` failed to unfold `SupportHomPair.Transport.derivedMap`". The old body is
restored verbatim; it is one delta step (of `Transport.coefficientGroupMap`) from the
coefficientGroupMap form, so the coordinate-pullback assembly still checks unchanged.

The original module contains `public import Sheaf.Paper.PurityAffineLineOrientationData`,
in addition to its original five public imports. No chosen objects, coefficients or signs
change. No target statement or target meaning changes. No new global attribute is set.

## Users

Every current transitive importer returned by `tools/downstream.py` is listed below.
Existing public imports and the re-export preserve the entire old public API, so no
adaptation is forced. Holders are the current recorded claims; these consumers are untouched.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensorComponents | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | K1 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | H1 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X8 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistRestrictionComponents | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | F4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | F1 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | G4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | V8 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | V3 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | G8 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | K4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | Z7 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | T3 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | H1 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | A4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | C3 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | F3 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | E2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | S2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | Y2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | B4 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | A3 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | T9 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | X2 | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same public declarations and definitions via re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public declarations and definitions via re-export; no adaptation. |

The directly named users of OrientationSupportData are the injectivity, uniqueness,
support-stalk and twisted-coordinate-sign modules. The coordinateBoundary users are
uniqueness and twisted-coordinate-sign. The restriction-map users are injectivity,
uniqueness and support-stalk. All use exactly the same public names and types. The
seven direct importers also keep every old public prerequisite from the original module.

## Status

landed 20261025T122613-L-1789949 2026-10-25 (merge of deliver/C4/Sheaf.Paper.PurityAffineLineOrientation)
