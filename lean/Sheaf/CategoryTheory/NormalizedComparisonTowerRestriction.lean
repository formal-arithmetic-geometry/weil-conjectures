module

public import Mathlib.CategoryTheory.Whiskering

/-! # Restricted normalized comparison paths in a coefficient tower

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md, (3), final compatibility sentence.
(blueprint: lem-sfb-normalized-comparison-tower-restriction)

The two path definitions below are composites of the specified natural isomorphisms.
The statement identifies their normalized restrictions as natural transformations.
-/

@[expose] public section

set_option autoImplicit false

universe vXr vXs vXt vSr vSs vSt uXr uXs uXt uSr uSs uSt

namespace CategoryTheory

/-- The left coefficient-tower path `Eᵗ(tS) ∘ hst ∘ FXst(hrs)`, naturally in the input.
Source: scalar-six pullback proof (3), coefficient-associativity compatibility.
(blueprint: lem-sfb-normalized-comparison-tower-restriction) -/
def normalizedComparisonTowerLeftPath
    {Xr : Type uXr} [Category.{vXr} Xr] {Xs : Type uXs} [Category.{vXs} Xs]
    {Xt : Type uXt} [Category.{vXt} Xt] {Sr : Type uSr} [Category.{vSr} Sr]
    {Ss : Type uSs} [Category.{vSs} Ss] {St : Type uSt} [Category.{vSt} St]
    (Er : Sr ⥤ Xr) (Es : Ss ⥤ Xs) (Et : St ⥤ Xt)
    (FXrs : Xr ⥤ Xs) (FXst : Xs ⥤ Xt)
    (FSrs : Sr ⥤ Ss) (FSst : Ss ⥤ St) (FSrt : Sr ⥤ St)
    (hrs : Er ⋙ FXrs ≅ FSrs ⋙ Es) (hst : Es ⋙ FXst ≅ FSst ⋙ Et)
    (tS : FSrs ⋙ FSst ≅ FSrt) :
    Er ⋙ FXrs ⋙ FXst ⟶ FSrt ⋙ Et :=
  Functor.whiskerRight hrs.hom FXst ≫ Functor.whiskerLeft FSrs hst.hom ≫
    Functor.whiskerRight tS.hom Et

/-- The right coefficient-tower path `hrt ∘ tX(Eʳ)`, naturally in the input.
Source: scalar-six pullback proof (3), coefficient-associativity compatibility.
(blueprint: lem-sfb-normalized-comparison-tower-restriction) -/
def normalizedComparisonTowerRightPath
    {Xr : Type uXr} [Category.{vXr} Xr] {Xs : Type uXs} [Category.{vXs} Xs]
    {Xt : Type uXt} [Category.{vXt} Xt] {Sr : Type uSr} [Category.{vSr} Sr]
    {St : Type uSt} [Category.{vSt} St]
    (Er : Sr ⥤ Xr) (Et : St ⥤ Xt)
    (FXrs : Xr ⥤ Xs) (FXst : Xs ⥤ Xt) (FXrt : Xr ⥤ Xt) (FSrt : Sr ⥤ St)
    (hrt : Er ⋙ FXrt ≅ FSrt ⋙ Et) (tX : FXrs ⋙ FXst ≅ FXrt) :
    Er ⋙ FXrs ⋙ FXst ⟶ FSrt ⋙ Et :=
  Functor.whiskerLeft Er tX.hom ≫ hrt.hom

/-- Both coefficient-tower paths have the common normalized restricted value (L),
as natural transformations; their restrictions are consequently equal.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md, (3), final sentence.
(blueprint: lem-sfb-normalized-comparison-tower-restriction)

Proof plan (the node's seven elementary steps):
1. Fix `M`, put `U = Er(M)`, and expand the two paths and the common composite.
   Use the associativity and identity laws of `def-nagata-category` throughout.
2. For the left path, expand `Lt.map` of the composite. Naturality of `ρt` at
   `tS(M)` moves this component outside; apply normalization `Nst` at `FSrs(M)`.
3. Naturality of `qst` at `hrs(M)` moves this component past `Lt(FXst(hrs(M)))`.
4. Substitute normalization `Nrs` at `M` and distribute `FSst` over composition.
   This is precisely the displayed common value.
5. For the right path, use normalization `Nrt` at `M`, then tower compatibility
   `Q` at `U` to replace the composite involving `tX` and `qrt`.
6. Naturality of `tS` at `ρr(M)` gives the same common value. Cancel the invertible
   component of `ρt` to obtain equality of the unnormalized restrictions.
7. Whiskering and vertical composition preserve naturality: for composable
   transformations, move a test arrow past each factor using its naturality square.
   Thus the component equalities are equalities of natural transformations.
-/
theorem normalizedComparisonTower_restriction
    {Xr : Type uXr} [Category.{vXr} Xr] {Xs : Type uXs} [Category.{vXs} Xs]
    {Xt : Type uXt} [Category.{vXt} Xt] {Sr : Type uSr} [Category.{vSr} Sr]
    {Ss : Type uSs} [Category.{vSs} Ss] {St : Type uSt} [Category.{vSt} St]
    (Lr : Xr ⥤ Sr) (Ls : Xs ⥤ Ss) (Lt : Xt ⥤ St)
    (Er : Sr ⥤ Xr) (Es : Ss ⥤ Xs) (Et : St ⥤ Xt)
    (ρr : Er ⋙ Lr ≅ 𝟭 Sr) (ρs : Es ⋙ Ls ≅ 𝟭 Ss) (ρt : Et ⋙ Lt ≅ 𝟭 St)
    (FXrs : Xr ⥤ Xs) (FXst : Xs ⥤ Xt) (FXrt : Xr ⥤ Xt)
    (FSrs : Sr ⥤ Ss) (FSst : Ss ⥤ St) (FSrt : Sr ⥤ St)
    (qrs : FXrs ⋙ Ls ≅ Lr ⋙ FSrs) (qst : FXst ⋙ Lt ≅ Ls ⋙ FSst)
    (qrt : FXrt ⋙ Lt ≅ Lr ⋙ FSrt)
    (hrs : Er ⋙ FXrs ≅ FSrs ⋙ Es) (hst : Es ⋙ FXst ≅ FSst ⋙ Et)
    (hrt : Er ⋙ FXrt ≅ FSrt ⋙ Et)
    (Nrs : ∀ M : Sr, Ls.map (hrs.hom.app M) ≫ ρs.hom.app (FSrs.obj M) =
      qrs.hom.app (Er.obj M) ≫ FSrs.map (ρr.hom.app M))
    (Nst : ∀ M : Ss, Lt.map (hst.hom.app M) ≫ ρt.hom.app (FSst.obj M) =
      qst.hom.app (Es.obj M) ≫ FSst.map (ρs.hom.app M))
    (Nrt : ∀ M : Sr, Lt.map (hrt.hom.app M) ≫ ρt.hom.app (FSrt.obj M) =
      qrt.hom.app (Er.obj M) ≫ FSrt.map (ρr.hom.app M))
    (tX : FXrs ⋙ FXst ≅ FXrt) (tS : FSrs ⋙ FSst ≅ FSrt)
    (Q : ∀ U : Xr, Lt.map (tX.hom.app U) ≫ qrt.hom.app U =
      qst.hom.app (FXrs.obj U) ≫ FSst.map (qrs.hom.app U) ≫ tS.hom.app (Lr.obj U)) :
    (Functor.whiskerRight
        (normalizedComparisonTowerLeftPath Er Es Et FXrs FXst FSrs FSst FSrt hrs hst tS) Lt ≫
      Functor.whiskerLeft FSrt ρt.hom =
      Functor.whiskerLeft (Er ⋙ FXrs) qst.hom ≫
        Functor.whiskerRight (Functor.whiskerLeft Er qrs.hom) FSst ≫
        Functor.whiskerRight (Functor.whiskerRight ρr.hom FSrs) FSst ≫ tS.hom) ∧
    (Functor.whiskerLeft (Er ⋙ FXrs) qst.hom ≫
        Functor.whiskerRight (Functor.whiskerLeft Er qrs.hom) FSst ≫
        Functor.whiskerRight (Functor.whiskerRight ρr.hom FSrs) FSst ≫ tS.hom =
      Functor.whiskerRight
        (normalizedComparisonTowerRightPath Er Et FXrs FXst FXrt FSrt hrt tX) Lt ≫
      Functor.whiskerLeft FSrt ρt.hom) ∧
    Functor.whiskerRight
        (normalizedComparisonTowerLeftPath Er Es Et FXrs FXst FSrs FSst FSrt hrs hst tS) Lt =
      Functor.whiskerRight
        (normalizedComparisonTowerRightPath Er Et FXrs FXst FXrt FSrt hrt tX) Lt := by
  have hL (M : Sr) :
      Lt.map ((normalizedComparisonTowerLeftPath Er Es Et FXrs FXst
        FSrs FSst FSrt hrs hst tS).app M) ≫ ρt.hom.app (FSrt.obj M) =
      qst.hom.app (FXrs.obj (Er.obj M)) ≫ FSst.map (qrs.hom.app (Er.obj M)) ≫
        FSst.map (FSrs.map (ρr.hom.app M)) ≫ tS.hom.app M := by
    simp only [normalizedComparisonTowerLeftPath, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc]
    have ht := ρt.hom.naturality (tS.hom.app M)
    have hq := qst.hom.naturality (hrs.hom.app M)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at ht hq
    rw [ht, ← Category.assoc (Lt.map (hst.hom.app (FSrs.obj M))), Nst (FSrs.obj M)]
    simp only [Category.assoc]
    rw [← Category.assoc (Lt.map (FXst.map (hrs.hom.app M))), hq]
    simp only [Category.assoc]
    rw [← Category.assoc (FSst.map (Ls.map (hrs.hom.app M))),
      ← FSst.map_comp, Nrs, FSst.map_comp]
    simp only [Category.assoc]
  have hR (M : Sr) :
      Lt.map ((normalizedComparisonTowerRightPath Er Et FXrs FXst
        FXrt FSrt hrt tX).app M) ≫ ρt.hom.app (FSrt.obj M) =
      qst.hom.app (FXrs.obj (Er.obj M)) ≫ FSst.map (qrs.hom.app (Er.obj M)) ≫
        FSst.map (FSrs.map (ρr.hom.app M)) ≫ tS.hom.app M := by
    simp only [normalizedComparisonTowerRightPath, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [Nrt, ← Category.assoc, Q]
    have ht := tS.hom.naturality (ρr.hom.app M)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at ht
    simp only [Category.assoc]
    rw [← ht]
  refine ⟨?_, ?_, ?_⟩
  · ext M
    exact hL M
  · ext M
    exact (hR M).symm
  · ext M
    apply (cancel_mono (ρt.hom.app (FSrt.obj M))).mp
    exact (hL M).trans (hR M).symm

end CategoryTheory
