# AlgebraicGeometry.Scheme.finiteRingCompactSupportProjection

## Reason

The intrinsic projection is a concrete composition of derived realization and inverse
realization functors. Unfolding and evaluating it in an invertibility proof repeatedly
expanded the same equivalence and exact-derived functor constructions; even an isolated
component-conversion proof exceeded the single-file compilation limit. The source library
explains this nested-proof conversion failure in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` and uses bundled constants
and abstract categorical interfaces to avoid it.

The map module is unclaimed in the current claim records. No adopted source-library file
is changed. The new generic realization API performs the original precomposition and
postcomposition. The stored derived equivalence is exactly the result of deriving the
original `sfIntrinsicModuleEquivalence`, with the same functor and inverse. The abelian structure and small derived-category model are the existing ones found by
instance search, stored once with atomic scalar parameters; their use as instances is local.
No new mathematical assumption or data chosen from an existence theorem is introduced.
A local priority for `CommRing.toRing` keeps the abstract scalar interface and its
`ULift` specialization on the same definitionally equal ring structure. This avoids
rechecking the entire derived-category construction through the `ULift.ring` diamond.

## Old

```lean
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (Functor.postcompose₂.obj
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategory).map
      (((((Functor.whiskeringLeft₂ _).obj
        (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory).obj
          (sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory)).map
            (ProEtale.projectionMapOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c))
```

## New

```lean
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  sfRealizeCompactificationProjection
    (sfIntrinsicDerivedModuleEquivalence X R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).functor
    (sfFixedCompactificationProjection (ULift.{u + 1, u} R) c)
```

The implementation companions are:

- `sfRealizeCompactificationProjection`
- `isIso_sfRealizeCompactificationProjection_app_app`
- `sfFixedSheafAbelian`
- `sfFixedDerivedCategoryModel`
- `sfIntrinsicDerivedModuleEquivalence`
- `sfFixedCompactificationProjectionSource`
- `sfFixedCompactificationProjectionTarget`
- `sfFixedCompactificationProjection`

Their complete definitions and the proved component API are in the same module. The standard
abelian structure and its existing derived-category model are cached together; the local
instance attributes ensure that all new interfaces share those exact data. The source and
target bifunctors are named to keep derived tensor instances out of later inferred types.
`Equivalence.mapDerivedCategory` uses `Equivalence.mk` with the original two derived functors;
its unit and counit are the derived coherence maps. The realization wrapper performs precisely
the original whiskering and postcomposition. No arbitrary endpoint isomorphism replaces the
projection arrow. The original public import list and explicit binders are preserved. Obsolete
private proof imports are removed.

## Users

The table includes every downstream module reported by `tools/downstream.py --uses`, plus
the map module itself. The direct uses of the original map are the assigned theorem and the arrow displays
in `SfExchanges` and `SfProEtaleProjectionFormula`. Those displays still describe exactly the same canonical arrow.
No target declaration signature changes. Because target statements use this definition,
the independent statement reader should reconfirm its unchanged canonical meaning.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SfEtaleExchanges` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | F6 | proof completed; same target statement |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SfExchanges` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassChern` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | same canonical morphism and statement; no source edit |
| `Sheaf.Paper.FiniteRingCompactSupportProjectionMap` | unclaimed | generic API and cached realization; same canonical arrow |

The unchanged consumer modules `ConstructibleProjectionMates`, `SfExchanges` and
`SfProEtaleProjectionFormula` compile against the modified map. The assigned theorem and
map modules compile without errors or warnings. Their public import lists and the theorem
signature remain verbatim; no consumer source edit is required for these checks.

A further single-file check of unchanged `CompactSupportProjectionFormula` times out at
60 seconds, both against this map and in the published-map baseline control. Its source
is unchanged; the maintainer's global build checks the full consumer closure.

## Status

landed 20261020T211710-L-3489856 2026-10-20 (merge of deliver/F6/Sheaf.Paper.FiniteRingCompactSupportProjection)
