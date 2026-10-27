# Canonical ordinary finite single-object pullback constructions

## Reason

The unclaimed `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` retains every existing
signature, attribute and visibility. Only `ordinaryFiniteShiftedLinePullback` changes its body to specialize its identical
generic construction in `EtaleSinglePullbackComparisons`.
Its public import supplies that construction. Rebased onto current `sheaf-dag`, including
X7 commit `69211e87b70`, for return A1. The current canonical single-functor caches,
`ordinaryFiniteSingleExactPullbackIso`, `ordinaryFiniteSinglePullbackIso`, all three
X7 comparison statements, and the local `implicit_reducible` and instance attributes
are retained verbatim. The generic constructor accepts X7's cached single functors and comparison
explicitly, so the shifted comparison equation retains its original `rfl` proof. The current `ordinaryFiniteUnitPullback` body is the
single-iso factorization shown below; it is not `genericConstantIso`.
The generic comparison API uses `genericConstantIso` internally, and its relationship
to the ordinary single-iso factorization is proved without changing that definition.
No object, map, signature, attribute or choice changes.

The shifted construction applies shift commutation, then shifts the single
comparison followed by the supplied coefficient isomorphism. Unfolding the cache
recovers exactly the original construction. This avoids repeatedly elaborating
its concrete module-category structures in the composition calculation. No data
is chosen and no coefficient normalization changes.

The generic comparison API proves its constant component equation and identifies
that component with the source constant comparison by associativity. No vector-descent edit is included; its proof and signatures remain unchanged.
Definitions reached by targets require the normal statement review again.

## Old

```lean
def ordinaryFiniteShiftedLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  ((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((ordinaryFiniteSinglePullbackIso A f).app _ ≪≫
        (ordinaryFiniteSingleFunctor A X).mapIso (t.line f hY))
```

## New

```lean
def ordinaryFiniteShiftedLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  shiftedSinglePullbackIsoWith (ModuleCat.{u + 1} A) f
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (ordinaryFiniteSinglePullbackIso A f)
    (Scheme.finiteEtaleTateLine Y N A hA) (Scheme.finiteEtaleTateLine X N A hA)
    (t.line f hY) 2
```

The current constant-object body retained from the shared source is:

```lean
(ordinaryFiniteSinglePullbackIso A f).app _ ≪≫
  (ordinaryFiniteSingleFunctor A X).mapIso
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))
```

`constantSinglePullbackIso B f M` reuses `genericConstantIso B M f`; unfolding that
existing constructor gives exactly the same single-complex comparison followed by
the single functor applied to the constant-sheaf pullback comparison.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineLinearActionFamily` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` | unclaimed | Only the shifted comparison changes; X7's single-iso unit comparison, equation lemmas and local attributes are retained. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationIdentityUnit` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationMate` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationSwapLocal` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent` | unclaimed | No edit included; the consumer check passes, with variable compilation timing. |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.ProEtaleVectorIntegration` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | U7 | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.SectionCoordinateCounitNormalization` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.SupportedProjectiveChern` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.UniversalTranslationMultiplier` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | P2 | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.SixFunctors.ProjectiveLineTraceModel` | unclaimed | Public interfaces and mathematical maps unchanged; existing consumers checked without adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransportData` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.SfP1ChartExchange` | E2 | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange` | X7 | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate` | X5 | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange` | unclaimed | Same canonical shifted comparison; no adaptation included (reviewer 2026-10-27: the unchanged module compiles against the new body in 11 s, its `unfold` followed by `exact shiftedSingle_eq` closes by definitional unfolding). |
| `Sheaf.AlgebraicGeometry.SfP1CoordinateIntegrals` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.SmoothPurity.FiniteP1CoordinateKernel` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange` | unclaimed | Same canonical shifted comparison; no adaptation included. |
| `Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange` | unclaimed | Same canonical shifted comparison; no adaptation included. |

## Current comparison consumer checks

Return A1 requires recompiling the current X7-adapted
`FiniteP1ChernMapBaseChange` and `VectorIntegrationIdentityUnit`, as well as the
packet modules using the changed shifted comparison. The unchanged consumers are
checked as temporary copies and are not included in the delivery.
The clean checks accept the arrows file, twisted-unit helper, packet composition API and ordinary unit-normalization consumer against the retained definitions. The three proved normalization helpers also compile within the per-file limit. In particular,
`ordinaryFiniteShiftedLinePullback_eq` retains its statement and original `rfl` proof.
The generic constructor takes the existing cached single functors and comparison
explicitly, avoiding conversion between two separately assembled single functors.
The importer checks also compile the unchanged current Kummer source temporarily,
because the first compiler baseline lacked its newly landed public declarations. Both unchanged X7-adapted importers pass against the repaired arrows and current Kummer dependency. Their temporary sources are excluded from the delivery.

The concrete constant-component specialization, ordinary-to-canonical comparison,
and canonical unit square are compiled separately before the ordinary unit theorem.
Each helper has a complete proof. These boundaries cache the large structural
conversions while retaining X7's single-iso ordinary unit body verbatim.

## Status

landed 20261027T135451-L-3711227 2026-10-27 (merge of deliver/Z8/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit)
