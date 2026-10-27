# AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_kummer_chern_realization_of_boundary

## Reason

STATEMENT-DISPUTED: the old statement permits every target isomorphism t, but its
boundary hypothesis does not depend on t. For l=3, E=Q_3, n=0 and P¹ over an
algebraically closed field of characteristic zero, the positive Kummer class of
O(1) is nonzero of order three. Replacing a normalized t by -t changes the left
side's sign and leaves the right side fixed. The source uses the section-normalized
comparison, so require equality with that concrete comparison.

The sole caller needs an existential isomorphism. Its proof now constructs the
canonical composite and supplies the new equality by reflexivity. Its entire
public interface remains verbatim. The source library under WeilConjectures is
untouched. No Challenge target statement changes.

The FiniteP1BoundaryData body is factored through the definition
FiniteKummerBoundary to share category witnesses during kernel checking. Unfolding
the new definition gives exactly its old body; this is a definitional refactoring,
with the same signature and the same mathematical meaning for every target.
Profiler evidence: the initially repeated ordinary boundary expression took 86.9 s
in kernel checking. The shared boundary definition compiles in 37.9 s, the
coordinate construction in 28.5 s, and its ordinary boundary statement in 6.9 s.
The independent definition and coordinate files were separated after identifying
and factoring this repeated expression; no time limit was raised.

## Old

```lean
theorem finiteP1_kummer_chern_realization_of_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2))
    (hb : FiniteP1BoundaryData l E e cX n) :
    (SpTowerShriek.Ev l E X n).map
        (firstChern l E cX
          (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
      (finiteOverUnitCoordinate l E n e c).hom ≫
        (finiteOverRealization l E n e).map
          ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
            (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _)
              (ULift.ext _ _ (coefficient_annihilates l E n)) S
              (by simpa only [Nat.cast_pow] using hS.pow (n + 1))))
```

```lean
def FiniteP1BoundaryData
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] : Prop :=
  finiteBoundaryEquality
    ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map
      (finiteQuotient l E X n))
    (((DerivedCategory.singleFunctor (DiagonalAb X) 0).map
      (finiteRootMap l E X n))⟦(2 : ℤ)⟧')
    (mapSingleArrow (finiteForget l E X n) (2 : ℤ)
      (evaluatedChern l E cX
        (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n))
    (mapSingleArrow (abEvaluation X n) (2 : ℤ)
      (kummerComposite (C := Ab X)
        (ShortComplex.mk cX.kummer.inclusion cX.kummer.power cX.kummer.zero)
        cX.kummer.exact
        (lineBundleClass X (Scheme.Pic.mapHom e.hom (hyperplanePic S)))))
```

## New

```lean
theorem finiteP1_kummer_chern_realization_of_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2))
    (ht : t = finiteP1KummerCoordinate l E n e cX hS c)
    (hb : FiniteP1BoundaryData l E e cX n) :
    (SpTowerShriek.Ev l E X n).map
        (firstChern l E cX
          (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
      (finiteOverUnitCoordinate l E n e c).hom ≫
        (finiteOverRealization l E n e).map
          ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
            (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _)
              (ULift.ext _ _ (coefficient_annihilates l E n)) S
              (by simpa only [Nat.cast_pow] using hS.pow (n + 1))))
```

```lean
def FiniteP1BoundaryData
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] : Prop :=
  FiniteKummerBoundary l E X n cX.kummer
    (Scheme.Pic.mapHom e.hom (hyperplanePic S))
    (evaluatedChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n)
```

finiteP1KummerCoordinate is a concrete composite of evaluation, single-complex,
section-normalized coefficient line, shift and pullback isomorphisms. Its data
does not come from an unproved existence assertion. The caller no longer chooses
a witness from FiniteP1KummerComparisonIso. The ordinary finite arrow used in the
proof is constructed independently of the tower Chern arrow.

## Users

The downstream scan is transitive. The only name consumer is
Sheaf.Paper.FiniteP1KummerChernRealization; it is the only direct importer. All
other rows retain their public statements, definitions and proofs unchanged.
The definition refactor preserves FiniteP1BoundaryData definitionally.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineLineAdjunctionAssembly | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientOrdinarySquare | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientPushAction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientRealization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientRootLineComparison | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientScalarPush | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedCoefficientSectionAction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedRootProjectionLinear | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.CompletedSupportedCoefficientTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalBaseSquares | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureLineComparison | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureLineEndpoint | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureOrdinaryLine | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureOrdinaryLineFactor | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureOrdinaryLineFactorIso | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalClosureScalarFrame | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientArrowTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientCategory | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientExchange | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFamilyExtension | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFiniteClosure | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFiniteExtension | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientMaps | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientPullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientQuotients | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientReference | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientScalars | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedClassPullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedFrame | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedPullbackCompatibility | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedPushSquare | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCompletedTracePullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicCartierFrame | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicCartierProjection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicClassRestriction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicEvaluationTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicRootEndpoint | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalCyclicUniformizerSquare | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteArrowEquations | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteCartierClassToArrow | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteCartierScalarCancellation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteIntegralEndpoint | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteOrdinaryComparisons | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteRootMap | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteScalarSquares | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteTraceChernCriterion | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFiniteTracePresentation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalFlatScalarEndpoint | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalIntegralRootLevelScalars | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalIntegralRootMap | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalPullbackSquares | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientBaseChange | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientClassPullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientRootEndpoint | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientRootProjectionIso | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientSourcePullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalQuotientTracePullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalScalarCompatibilityTriangle | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalScalarDiagramTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalScalarEndpointComposition | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalScalarPullbackCompatibility | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalScalarRestrictionComposition | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalSupportedAcyclic | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalSupportedFlat | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalSupportedOrdinaryScalars | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalSupportedScalarSource | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTowerCoefficients | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTowerTrace | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceFiniteChernCohomology | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceFiniteChernComparison | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceFiniteIntegralProjection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceFiniteSplitting | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceLimitWitnessExistence | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceModelTraceComponents | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTracePresentationExistence | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceResultExistence | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalTraceTwistedSplittingComponents | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerAdjunctConditions | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerAdjunctTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerAnnihilator | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerCartierReduction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerChernNormalization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerChernTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerFiniteModels | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerFiniteNormalization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerLocalChern | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerLocalEndpoints | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerRootFrame | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerScalarFrame | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerScalarSquares | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerTraceChernDegree | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.DiagonalUniformizerTraceReduction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.FiniteP1KummerChernRealization | unclaimed (current server claim checked) | Proof selects the canonical comparison; every public signature and definition stays verbatim. |
| Sheaf.Paper.ProjectiveDiagonalComposition | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.ProjectiveDiagonalPullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.ProjectiveNormalizedUnitCounitRestriction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.ProjectiveSupportedSectionProjection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1AmbientComposites | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1AmbientTail | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1CompletedChernDegree | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1CounitInversionCondition | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1DiagonalTensor | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1FirstAmbientContraction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1FirstTraceTransport | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1KernelContractions | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1LineFromPreservation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1LocalizingPreservation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1LocalizingProjection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1PositiveLineConstructible | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ProjectionNaturality | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernBaseChange | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernDegree | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernMaps | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernP2Degree | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernQDegree | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1ScalarChernSplittings | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondAmbientContraction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondPretrace | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondPullComparison | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondPullSection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondScalarTrace | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondTraceEquation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SecondTraceReordering | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1SectionEvaluation | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1TensorShiftNaturality | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1Triangle | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1UnitCounit | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1UnitFactorization | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalP1UnitInversionCondition | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.RationalTatePullback | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.TateTwistedProjection | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralKernelContractions | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralNormalizedFamily | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Targets.AffineSpaceRationalLine | not adapted | No reference to the changed theorem; inherits the unchanged existential realization interface. No source change. |
| Sheaf.Paper.FiniteP1KummerBoundaryTransport | D3 | Missing normalization premise repaired; proof assembled from finite generator detection and ordinary boundary. |

## Status

landed 20261027T233846-L-4124344 2026-10-27 (merge of deliver/D3/Sheaf.Paper.FiniteP1KummerBoundaryTransport)
