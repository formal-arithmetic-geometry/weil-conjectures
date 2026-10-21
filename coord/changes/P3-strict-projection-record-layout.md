# Strict projection records: abstract data interfaces

## Reason

Replace the two native records by specializations of generic data records. Their
categories, localization functors and canonical categorical structures are explicit
parameters of the generic records. Group data fields before proof fields and name the
original native counit equation `RingedTensorEdge.ProjectionCounitNormalized`. This
avoids repeatedly elaborating dependent module-sheaf and derived-category interfaces.
Every native mathematical requirement is retained.

`StrictProjectionLimit A` fixes the generic categories and both localization functors
to precisely the original derived module and strict-tower categories and their `Q`.
The categorical structures and localization instances come from those same derived
categories. Its fields impose exactly the original derived-limit, evaluation, Roos,
and naturality conditions. There is no extra hypothesis on `A`.

`StrictProjectionDirectImage e lx ly` fixes the four generic localization functors,
ordinary and derived pushforward functors, limit records and counit predicate to their
original values. In particular its `counit_normalized` field is exactly the old equation;
the native alias cannot choose a weaker predicate. Both records retain all original
field names and types after specialization.

The native type names and field notation remain usable. Generated constructor and
fully qualified projection names move to `StrictProjectionLimitData` and
`StrictProjectionDirectImageData`, and positional constructor order changes. There
are no external consumers to adapt. This is a representation repair preserving the
mathematical statement.

The complete theorem signature and original docstring of
`SheafOfModules.ringedStrictTowerProjectionMorphism` remain verbatim, as do the public
imports. No declaration in `Challenge.lean` or in the adopted source tree is changed.
The independent statement reader must check that the new native specializations impose
exactly the old requirements. All data definitions construct actual data or abbreviate
existing data; none contains a hole or chooses an arbitrary unproved witness.

## Old

```lean
structure StrictProjectionLimit (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] where
  L : DerivedCategory A.projectionTowers ⥤ A.mateDerived
  eta : (lim : A.projectionTowers ⥤ A.mateModules).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso A.projectionTowers (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex A.projectionTowers ℤ, I.IsKInjective → IsIso (eta.app I)
  ev : DerivedCategory A.projectionTowers ⥤ (ℕᵒᵖ ⥤ A.mateDerived)
  evaluation : DerivedCategory.Q ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost DerivedCategory.Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

structure StrictProjectionDirectImage {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y) where
  eta : e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ e.right
  derived : e.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso X.mateModules (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective → IsIso (eta.app I)
  counit_normalized : ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective →
    e.left.map (eta.app I) ≫ e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      derivedPullbackComplexComparison e.pullback e.left e.epsilon
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
  Rt : DerivedCategory X.projectionTowers ⥤ DerivedCategory Y.projectionTowers
  towerEta : e.projectionTowerPushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rt
  towerDerived : Rt.IsRightDerivedFunctor towerEta
    (HomologicalComplex.quasiIso X.projectionTowers (ComplexShape.up ℤ))
  towerComputes : ∀ I : CochainComplex X.projectionTowers ℤ,
    I.IsKInjective → IsIso (towerEta.app I)
  evaluation : Rt ⋙ ly.ev ≅ lx.ev ⋙ projectionPost e.right
  evaluation_normalized : ∀ (I : CochainComplex X.projectionTowers ℤ), I.IsKInjective →
    ∀ n : ℕᵒᵖ,
      (ly.ev.map (towerEta.app I)).app n ≫
          (evaluation.hom.app (DerivedCategory.Q.obj I)).app n ≫
          e.right.map ((lx.evaluation.hom.app I).app n) =
        (ly.evaluation.hom.app
          ((e.projectionTowerPushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).app n ≫
          eta.app (I.asFunctor.obj n)
  ordinary : (lim : X.projectionTowers ⥤ X.mateModules) ⋙ e.pushforward ≅
    e.projectionTowerPushforward ⋙ (lim : Y.projectionTowers ⥤ Y.mateModules)
  ordinary_normalized : ∀ H, ordinary.hom.app H = limit.post H e.pushforward
  a : lx.L ⋙ e.right ≅ Rt ⋙ ly.L
  normalized : ∀ I : CochainComplex X.projectionTowers ℤ,
    eta.app (((lim : X.projectionTowers ⥤ X.mateModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) ≫ e.right.map (lx.eta.app I) ≫
        a.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom
        (ComplexShape.up ℤ)).app I) ≫
        ly.eta.app ((e.projectionTowerPushforward.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫ ly.L.map (towerEta.app I)
```

## New

```lean
structure StrictProjectionLimitData (B : Type uB) [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasCountableProducts DB]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))] where
  L : DT ⥤ DB
  eta : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ Q ⟶ QT ⋙ L
  ev : DT ⥤ (ℕᵒᵖ ⥤ DB)
  evaluation : QT ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (eta.app I)
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

abbrev StrictProjectionLimit (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] :=
  StrictProjectionLimitData A.mateModules DerivedCategory.Q DerivedCategory.Q

structure StrictProjectionDirectImageData
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasLimitsOfShape ℕᵒᵖ D]
    {DB DD TB TD : Type*} [Category* DB] [Category* DD] [Category* TB] [Category* TD]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasZeroObject DD] [HasShift DD ℤ] [Preadditive DD]
    [∀ n : ℤ, (shiftFunctor DD n).Additive] [Pretriangulated DD]
    [HasCountableProducts DB] [HasCountableProducts DD]
    (QY : CochainComplex B ℤ ⥤ DB) (QX : CochainComplex D ℤ ⥤ DD)
    (QTY : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ TB)
    (QTX : CochainComplex (ℕᵒᵖ ⥤ D) ℤ ⥤ TD)
    [QX.IsLocalization (HomologicalComplex.quasiIso D (.up ℤ))]
    [QTY.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    [QTX.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ))]
    (V : D ⥤ B) [V.Additive] (R : DD ⥤ DB)
    (lx : StrictProjectionLimitData D QX QTX) (ly : StrictProjectionLimitData B QY QTY)
    (CounitNormalized : (V.mapHomologicalComplex (.up ℤ) ⋙ QY ⟶ QX ⋙ R) → Prop) where
  eta : V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
    QX ⋙ R
  Rt : TD ⥤ TB
  towerEta : (projectionPost V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    QTY ⟶ QTX ⋙ Rt
  evaluation : Rt ⋙ ly.ev ≅ lx.ev ⋙ projectionPost R
  ordinary : (lim : (ℕᵒᵖ ⥤ D) ⥤ D) ⋙ V ≅
    (projectionPost V) ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  a : lx.L ⋙ R ≅ Rt ⋙ ly.L
  derived : R.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex D ℤ, I.IsKInjective → IsIso (eta.app I)
  counit_normalized : CounitNormalized eta
  towerDerived : Rt.IsRightDerivedFunctor towerEta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (ComplexShape.up ℤ))
  towerComputes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
    I.IsKInjective → IsIso (towerEta.app I)
  evaluation_normalized : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ), I.IsKInjective →
    ∀ n : ℕᵒᵖ,
      (ly.ev.map (towerEta.app I)).app n ≫
          (evaluation.hom.app (QTX.obj I)).app n ≫
          R.map ((lx.evaluation.hom.app I).app n) =
        (ly.evaluation.hom.app
          (((projectionPost V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).app n ≫
          eta.app (I.asFunctor.obj n)
  ordinary_normalized : ∀ H, ordinary.hom.app H = limit.post H V
  normalized : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
    eta.app (((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) ≫ R.map (lx.eta.app I) ≫
        a.hom.app (QTX.obj I) =
      QY.map ((NatTrans.mapHomologicalComplex ordinary.hom
        (ComplexShape.up ℤ)).app I) ≫
        ly.eta.app (((projectionPost V).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫ ly.L.map (towerEta.app I)

def RingedTensorEdge.ProjectionCounitNormalized
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    (eta : e.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ e.right) : Prop :=
  ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective →
          e.left.map (eta.app I) ≫ e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
            derivedPullbackComplexComparison e.pullback e.left e.epsilon
              ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map
              ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)

abbrev StrictProjectionDirectImage {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y) :=
  StrictProjectionDirectImageData DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q e.pushforward e.right lx ly
    e.ProjectionCounitNormalized
```

## Users

Read-only searches of `lean/Sheaf/`, `lean/WeilConjectures/`, `lean/Challenge.lean`,
and preserved Lean files in `coord/` found no external reference to either record and
no importer of this module. This inventory was repeated on 2026-10-21. There is no
positional constructor consumer to adapt. No source-library module and no other
group's module is changed.

The project's `downstream.py` scanner registers a repository-local cache write at exit.
It was stopped before exit to respect the read-only checkout; the consumer inventory
above uses source searches.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | P3 | Native records specialize generic data records with identical requirements; theorem proof completed. |

## Status

landed 20261021T020132-L-2589758 2026-10-21 (merge of deliver/P3/Sheaf.Paper.RingedStrictTowerProjectionMorphism)
