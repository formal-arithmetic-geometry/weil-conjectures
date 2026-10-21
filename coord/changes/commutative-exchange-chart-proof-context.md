# AlgebraicGeometry.Etale.commutativeExchangeChart

## Reason

The proof adds file-level elaboration options and local instance/reducibility
attributes. The static interface check classifies these additional commands as
an interface change and requires this record. They keep derived-functor
expressions abstract during the new proof and cache existing etale/sheafification
instances. The instance declarations are existing property proofs; proof
irrelevance identifies them with the original instances. The reducibility
attributes are local and affect elaboration, not any definition's value.

Every existing public signature, public import, and the complete bodies of the
six existing definitions are preserved verbatim. No mathematical statement or
definition is repaired or changed. In particular, this delivery changes no
hypothesis, universe or conclusion, and does not reopen a target's meaning.

## Old

The theorem's signature was:

```lean
theorem commutativeExchangeChart
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q U x =
        exchangeChartTheta f' _ q (g.Etale.obj U) (exchangeChartPullback sq F q U x)) ∧
    (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G)
      (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq G q U
        (rawRestrictedCohomologyComparison f q G U
          (rawRestrictedCohomologyClass f q F U x ≫
            (shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((g')^*[AddCommGrpCat.{u + 1}]).map φ)))).hom.app (op (g.Etale.obj U))
        (exchangeChartValue sq F q U x)) ∧
    (∀ (U V : Y.Etale) (i : V ⟶ U) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q V
        (rawRestrictedCohomologyComparison f q F V
          ((abelianHigherDirectImageRawPresheaf f q F).map i.op
            (rawRestrictedCohomologyClass f q F U x))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((g')^*[AddCommGrpCat.{u + 1}]).obj F)))).obj.map (g.Etale.map i).op
        (exchangeChartValue sq F q U x))
```

The file had `set_option autoImplicit false` and none of the additional proof
context commands listed below.

## New

The theorem has the identical signature:

```lean
theorem commutativeExchangeChart
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q U x =
        exchangeChartTheta f' _ q (g.Etale.obj U) (exchangeChartPullback sq F q U x)) ∧
    (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G)
      (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq G q U
        (rawRestrictedCohomologyComparison f q G U
          (rawRestrictedCohomologyClass f q F U x ≫
            (shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((g')^*[AddCommGrpCat.{u + 1}]).map φ)))).hom.app (op (g.Etale.obj U))
        (exchangeChartValue sq F q U x)) ∧
    (∀ (U V : Y.Etale) (i : V ⟶ U) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q V
        (rawRestrictedCohomologyComparison f q F V
          ((abelianHigherDirectImageRawPresheaf f q F).map i.op
            (rawRestrictedCohomologyClass f q F U x))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((g')^*[AddCommGrpCat.{u + 1}]).obj F)))).obj.map (g.Etale.map i).op
        (exchangeChartValue sq F q U x))
```

The additional proof context is:

```lean
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Functor.mapDerivedCategoryPlus Functor.rightDerivedFunctorPlus
```

The existing `set_option autoImplicit false` is retained.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CommutativeExchangeChart --uses`
was run for the theorem and all six existing definitions. It found zero
current downstream Lean modules; each declaration occurs only in the item.
The two DAG parents below still plan to use its unchanged statement. Their
statements, definitions and proof plans require no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CommutativeExchangeChart | H9 | Proof elaboration context only; existing public interface and six definition bodies preserved. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageCohomologyKernel | unclaimed | Planned DAG consumer; unchanged statement remains applicable. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageRawLocalDescent | unclaimed | Planned DAG consumer; unchanged statement remains applicable. |

No module of the adopted `WeilConjectures` source tree is changed. No other
existing Lean module is adapted.

## Status

landed 20261021T014223-L-2389552 2026-10-21 (merge of deliver/H9/Sheaf.AlgebraicGeometry.CommutativeExchangeChart)
