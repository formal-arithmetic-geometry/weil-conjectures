/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits

import Sheaf.AlgebraicGeometry.RelativeHigherImageConeLaws
import Sheaf.Paper.KunHigherExchangeCoefficientCube
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Higher direct images along limits of cartesian squares

Source: Stacks Project, Tag 0EZT, second assertion, and Tag 0EYM
(blueprint: lem-kun-0ezt).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false


namespace Etale

private lemma square_iso_diagonal
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (d : X' ⟶ Y) (hd : d = g' ≫ f) (hd' : d = f' ≫ g) :
    squareUpperStarIso AddCommGrpCat.{u + 1} sq =
      (upperStarComp AddCommGrpCat.{u + 1} f' g d hd').symm ≪≫
        upperStarComp AddCommGrpCat.{u + 1} g' f d hd := by
  subst hd
  rfl

private lemma pullback_system_identity
    {X Y : Scheme.{u}} (e : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (squareUpperStarIso AddCommGrpCat.{u + 1}
      (show CommSq (𝟙 Y) e e (𝟙 X) from ⟨by simp⟩)).inv.app F ≫
      (upperStar AddCommGrpCat.{u + 1} e).map
        ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) =
    (upperStarId AddCommGrpCat.{u + 1} Y).hom.app
      ((upperStar AddCommGrpCat.{u + 1} e).obj F) := by
  rw [square_iso_diagonal _ e (by simp) (by simp)]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  rw [upperStarComp_id_left]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.assoc]
  have h := congrArg (fun t ↦ t.hom.app F)
    (upperStarComp_id_right AddCommGrpCat.{u + 1} e)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    Category.id_comp] at h
  rw [h, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp


private lemma pullback_system_composition
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    {e₀ : Y₀ ⟶ X₀} {e₁ : Y₁ ⟶ X₁} {e₂ : Y₂ ⟶ X₂}
    {a : X₁ ⟶ X₀} {b : X₂ ⟶ X₁} {c : X₂ ⟶ X₀}
    {x : Y₁ ⟶ Y₀} {y : Y₂ ⟶ Y₁} {z : Y₂ ⟶ Y₀}
    (sq₁ : CommSq x e₁ e₀ a) (sq₂ : CommSq y e₂ e₁ b)
    (sq : CommSq z e₂ e₀ c) (hc : c = b ≫ a) (hz : z = y ≫ x)
    (F₀ : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₂ : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁)
    (ψ : ((b)^*[AddCommGrpCat.{u + 1}]).obj F₁ ⟶ F₂) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sq).inv.app F₀ ≫
      ((e₂)^*[AddCommGrpCat.{u + 1}]).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a c hc).hom.app F₀ ≫
          ((b)^*[AddCommGrpCat.{u + 1}]).map φ ≫ ψ) =
    (upperStarComp AddCommGrpCat.{u + 1} y x z hz).hom.app
        (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀) ≫
      ((y)^*[AddCommGrpCat.{u + 1}]).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sq₁).inv.app F₀ ≫
          ((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} sq₂).inv.app F₁ ≫
      ((e₂)^*[AddCommGrpCat.{u + 1}]).map ψ := by
  subst hc
  subst hz
  have h := NatTrans.congr_app
    (squareUpperStarIso_paste_horiz_hom AddCommGrpCat.{u + 1} sq₁ sq₂ sq) F₀
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    TwoSquare.hComp_app, TwoSquare.mk, TwoSquare.natTrans] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (squareUpperStarIso AddCommGrpCat.{u + 1} sq₂).inv.naturality φ]
  apply (cancel_epi ((squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app F₀)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]

private lemma coherent_identity_transport
    {C D : Type*} [Category C] [Category D] {α β : Type*}
    (P : α → C ⥤ C) (Q : β → D ⥤ D) (U : C ⥤ D)
    (R : α → β → Prop) (S : ∀ a b, R a b → (P a ⋙ U ≅ U ⋙ Q b))
    {a a₀ : α} {b b₀ : β} (ha : a = a₀) (hb : b = b₀)
    (h : R a b) (h₀ : R a₀ b₀)
    (εP : P a₀ ⟶ 𝟭 C) (εQ : Q b₀ ⟶ 𝟭 D)
    (hbase : ∀ F : C, (S a₀ b₀ h₀).inv.app F ≫ U.map (εP.app F) =
      εQ.app (U.obj F)) (F : C) :
    (S a b h).inv.app F ≫ U.map
        (eqToHom (congrArg (fun t ↦ (P t).obj F) ha) ≫ εP.app F) =
      eqToHom (congrArg (fun t ↦ (Q t).obj (U.obj F)) hb) ≫ εQ.app (U.obj F) := by
  subst ha
  subst hb
  simpa only [eqToHom_refl, Category.id_comp] using hbase F

private lemma pullback_system_identity_transport
    {X Y : Scheme.{u}} (e : Y ⟶ X) (a : X ⟶ X) (x : Y ⟶ Y)
    (ha : a = 𝟙 X) (hx : x = 𝟙 Y) (sq : CommSq x e e a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sq).inv.app F ≫
      ((e)^*[AddCommGrpCat.{u + 1}]).map
        (eqToHom (congrArg (fun t : X ⟶ X ↦ ((t)^*[AddCommGrpCat.{u + 1}]).obj F) ha) ≫
          (upperStarId AddCommGrpCat.{u + 1} X).hom.app F) =
    eqToHom (congrArg (fun t : Y ⟶ Y ↦ ((t)^*[AddCommGrpCat.{u + 1}]).obj
        (((e)^*[AddCommGrpCat.{u + 1}]).obj F)) hx) ≫
      (upperStarId AddCommGrpCat.{u + 1} Y).hom.app
        (((e)^*[AddCommGrpCat.{u + 1}]).obj F) := by
  exact coherent_identity_transport
    (upperStar AddCommGrpCat.{u + 1}) (upperStar AddCommGrpCat.{u + 1})
    ((e)^*[AddCommGrpCat.{u + 1}]) (fun a x ↦ CommSq x e e a)
    (fun _ _ s ↦ squareUpperStarIso AddCommGrpCat.{u + 1} s) ha hx sq
    (show CommSq (𝟙 Y) e e (𝟙 X) from ⟨by simp⟩)
    (upperStarId AddCommGrpCat.{u + 1} X).hom
    (upperStarId AddCommGrpCat.{u + 1} Y).hom (pullback_system_identity e) F


private lemma pullback_system_projection
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    {e₀ : Y₀ ⟶ X₀} {e₁ : Y₁ ⟶ X₁} {e₂ : Y₂ ⟶ X₂}
    {a : X₁ ⟶ X₀} {b : X₂ ⟶ X₁} {c : X₂ ⟶ X₀}
    {x : Y₁ ⟶ Y₀} {y : Y₂ ⟶ Y₁} {z : Y₂ ⟶ Y₀}
    (sq₁ : CommSq x e₁ e₀ a) (sq₂ : CommSq y e₂ e₁ b)
    (sq : CommSq z e₂ e₀ c) (hc : c = b ≫ a) (hz : z = y ≫ x)
    (F : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((e₂)^*[AddCommGrpCat.{u + 1}]).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a c hc).hom.app F) ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} sq₂).hom.app
        (((a)^*[AddCommGrpCat.{u + 1}]).obj F) =
    (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} y x z hz).hom.app
        (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F) ≫
      ((y)^*[AddCommGrpCat.{u + 1}]).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sq₁).inv.app F) := by
  subst hc
  subst hz
  have h := NatTrans.congr_app
    (squareUpperStarIso_paste_horiz_hom AddCommGrpCat.{u + 1} sq₁ sq₂ sq) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    TwoSquare.hComp_app, TwoSquare.mk, TwoSquare.natTrans] at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]

private lemma pullback_coefficient_transition
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    {e₀ : Y₀ ⟶ X₀} {e₁ : Y₁ ⟶ X₁} {e₂ : Y₂ ⟶ X₂}
    {a : X₁ ⟶ X₀} {b : X₂ ⟶ X₁} {c : X₂ ⟶ X₀}
    {x : Y₁ ⟶ Y₀} {y : Y₂ ⟶ Y₁} {z : Y₂ ⟶ Y₀}
    (sq₁ : CommSq x e₁ e₀ a) (sq₂ : CommSq y e₂ e₁ b)
    (sq : CommSq z e₂ e₀ c) (hc : c = b ≫ a) (hz : z = y ≫ x)
    (F₀ : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁)
    {D₀ D₁ : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι₀ : D₀ ≅ ((c)^*[AddCommGrpCat.{u + 1}]).obj F₀)
    (ι₁ : D₁ ≅ ((b)^*[AddCommGrpCat.{u + 1}]).obj F₁)
    (dm : D₀ ⟶ D₁)
    (hd : dm ≫ ι₁.hom = ι₀.hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} b a c hc).hom.app F₀ ≫
      ((b)^*[AddCommGrpCat.{u + 1}]).map φ) :
    ((e₂)^*[AddCommGrpCat.{u + 1}]).map dm ≫
      ((e₂)^*[AddCommGrpCat.{u + 1}]).map ι₁.hom ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} sq₂).hom.app F₁ =
    ((e₂)^*[AddCommGrpCat.{u + 1}]).map ι₀.hom ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app F₀ ≫
      (upperStarComp AddCommGrpCat.{u + 1} y x z hz).hom.app
        (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀) ≫
      ((y)^*[AddCommGrpCat.{u + 1}]).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sq₁).inv.app F₀ ≫
          ((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) := by
  rw [← Functor.map_comp_assoc, hd]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (squareUpperStarIso AddCommGrpCat.{u + 1} sq₂).hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% pullback_system_projection sq₁ sq₂ sq hc hz F₀]

private lemma map_eq_of_comparison
    {C : Type*} [Category C] {X Y A B Z : C}
    (eX : X ≅ A) (eY : Y ≅ B) (m : X ⟶ Y) (a : A ⟶ Z) (b : Z ⟶ B)
    (h : m ≫ eY.hom = eX.hom ≫ a ≫ b) :
    m = eX.hom ≫ a ≫ b ≫ eY.inv := by
  have hs := congrArg (fun z ↦ z ≫ eY.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hs

private lemma isIso_of_isIso_colimit_comparison
    {J C : Type*} [Category J] [Category C] {D : J ⥤ C}
    (c : Cocone D) (hc : IsColimit c) {P : C} (m : c.pt ⟶ P)
    (hi : IsIso (hc.desc ⟨P, c.ι ≫ (Functor.const J).map m⟩)) : IsIso m := by
  have heq : hc.desc ⟨P, c.ι ≫ (Functor.const J).map m⟩ = m := by
    apply hc.hom_ext
    intro i
    exact hc.fac ⟨P, c.ι ≫ (Functor.const J).map m⟩ i
  exact heq ▸ hi

private lemma coefficient_square_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ E) (T : C ⥤ D) (U : D ⥤ E) (α : L ⟶ T ⋙ U)
    {A B : C} {A' B' : D} (β : A ⟶ B) (β' : A' ⟶ B')
    (a : T.obj A ⟶ A') (b : T.obj B ⟶ B')
    (hc : a ≫ β' = T.map β ≫ b)
    {X Y : E} (eX : X ⟶ L.obj A) (eY : Y ⟶ U.obj A') (m : X ⟶ Y)
    (hm : m ≫ eY = eX ≫ α.app A ≫ U.map a) :
    m ≫ eY ≫ U.map β' = eX ≫ L.map β ≫ α.app B ≫ U.map b := by
  rw [← Category.assoc, hm]
  simp only [Category.assoc, ← U.map_comp]
  rw [hc]
  simp only [U.map_comp]
  have hn := α.naturality β
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private lemma abelianHigherExchange_isIso_iff
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso (abelianHigherExchange sq F q) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let α := (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  let m := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  let γ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))
  change IsIso (α ≫ m ≫ γ) ↔ IsIso m
  exact (isIso_comp_left_iff α (m ≫ γ)).trans (isIso_comp_right_iff m γ)

private lemma relativeExchange_eq
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((g')^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') (q : ℕ) :
    relativeHigherImageExchange sq F F' φ q =
      abelianHigherExchange sq F q ≫
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map φ := by
  simp only [relativeHigherImageExchange, relativeHigherDirectImageExchange,
    rightDerivedLowerStarPlus, abelianHigherExchange,
    Functor.comp_map, Functor.map_comp, Category.assoc]

private lemma relativeExchange_cube
    {X₀ Y₀ S₀ T₀ X₁ Y₁ S₁ T₁ : Scheme.{u}}
    {h₀ : Y₀ ⟶ X₀} {e₀ : Y₀ ⟶ T₀} {f₀ : X₀ ⟶ S₀} {g₀ : T₀ ⟶ S₀}
    {h₁ : Y₁ ⟶ X₁} {e₁ : Y₁ ⟶ T₁} {f₁ : X₁ ⟶ S₁} {g₁ : T₁ ⟶ S₁}
    {x : X₁ ⟶ X₀} {y : Y₁ ⟶ Y₀} {s : S₁ ⟶ S₀} {a : T₁ ⟶ T₀}
    (sq₀ : ChosenCartesianSquare e₀ h₀ g₀ f₀)
    (sq₁ : ChosenCartesianSquare e₁ h₁ g₁ f₁)
    (sqf : CommSq x f₁ f₀ s) (sqg : CommSq a g₁ g₀ s)
    (sqh : CommSq y h₁ h₀ x) (sqe : CommSq y e₁ e₀ a)
    (F₀ : Sheaf T₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf T₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁) (q : ℕ) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sqf).inv.app
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F₀))) ≫
      ((f₁)^*[AddCommGrpCat.{u + 1}]).map
        (relativeHigherImageExchange sqg F₀ F₁ φ q) ≫
      abelianHigherExchange sq₁.toCommSq F₁ q =
    ((x)^*[AddCommGrpCat.{u + 1}]).map (abelianHigherExchange sq₀.toCommSq F₀ q) ≫
      relativeHigherImageExchange sqh
        (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀)
        (((e₁)^*[AddCommGrpCat.{u + 1}]).obj F₁)
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sqe).inv.app F₀ ≫
          ((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) q := by
  simpa only [relativeExchange_eq, Category.assoc] using
    abelianHigherExchange_coefficient_cube sq₀ sq₁ sqf sqg sqh sqe F₀ F₁ φ q

end Etale

open Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep inverse-image objects in their functorial form during endpoint comparison.
attribute [local irreducible] Etale.upperStar Etale.lowerStar

-- The immutable statement retains torsion; continuity works for all abelian sheaves.
set_option linter.unusedVariables false in
/-- A compatible inverse system of cartesian squares preserves a degreewise étale
base-change isomorphism on passing to its limit.

Source: Stacks Project, Tag 0EZT, second assertion (blueprint: lem-kun-0ezt).
The maps `φ` satisfy the identity and composition laws on the varying sites. The
isomorphisms `ιF` identify the forward diagram `D` with the pullbacks of these sheaves;
`hD` requires precisely the transition maps induced by `φ` and the cone projections.

Proof:
1. Construct the canonical diagram H of the sheaves s_i^* R^q g_i,* F_i, with the explicit
   exchange/coefficient transitions and projection comparison legs. The relative higher-image
   cone laws provide exactly its functor and cocone equations. Apply relative continuity for
   preorders (obtained by thin-skeleton reindexing) for g to its chosen colimit and these legs;
   its comparison is invertible, hence the canonical cocone cH itself is a colimit.
2. Inverse image f^* preserves colimits, so P=H followed by f^* has the colimit cocone cP=f^*cH.
   Pull the given coefficient diagram D and its colimit cocone along e^*. Define G_i=e_i^*F_i
   and its coefficient transitions using the commuting inverse-image square and e_j^*phi. The
   sheaf-level square pasting and composition coherence prove its identity and composition laws
   and identify the objects and maps of D followed by e^* with the canonical pullback system.
3. Let beta_i be the usual abelian-sheaf degree-q base-change map. Its two extra factors
   relative to the hypothesis are the invertible cohomology and degree-zero pullback
   comparisons; hence beta_i is invertible. Present P_i as r_i^* R^q h_i,* G_i by the projection
   square comparison followed by r_i^* beta_i. The coefficient cube theorem on the transition
   cube, combined with pullback-square coherence, gives precisely the required higher-image
   transition equation in this presentation.
4. Let beta be the limit abelian-sheaf exchange. Define the legs from P to its target as cP.ι_i
   followed by beta. Apply the coefficient cube theorem to the projection cube and the original
   coefficient coprojection. The coefficient-pullback equation identifies these legs with the
   projection exchanges for h and the pulled coefficient cocone. The h_i are qcqs as pullbacks
   of the g_i through their chosen cartesian presentations.
5. Apply relative continuity for preorders (obtained by thin-skeleton reindexing) for h with the
   same diagram P, the stage presentations through beta_i, the already known colimit cocone cP,
   and the just-verified canonical legs. It makes their descent invertible. The colimit
   universal property identifies that descent with beta, since their composites with every
   coprojection agree. Remove the invertible cohomology and single-functor comparison factors
   from beta to obtain exactly the stated cohomology of the limit derived exchange.
-/
theorem higherDirectImage_baseChange_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u})
    (cX : Cone DX) (hcX : IsLimit cX)
    (cY : Cone DY) (hcY : IsLimit cY)
    (cS : Cone DS) (hcS : IsLimit cS)
    (cT : Cone DT) (hcT : IsLimit cT)
    (ηf : DX ⟶ DS) (ηe : DY ⟶ DT) (ηg : DT ⟶ DS) (ηh : DY ⟶ DX)
    (f : cX.pt ⟶ cS.pt) (e : cY.pt ⟶ cT.pt)
    (g : cT.pt ⟶ cS.pt) (h : cY.pt ⟶ cX.pt)
    (hf : ∀ i : Iᵒᵖ, cX.π.app i ≫ ηf.app i = f ≫ cS.π.app i)
    (he : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηe.app i = e ≫ cT.π.app i)
    (hg : ∀ i : Iᵒᵖ, cT.π.app i ≫ ηg.app i = g ≫ cS.π.app i)
    (hh : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηh.app i = h ≫ cX.π.app i)
    (sq : ChosenCartesianSquare e h g f)
    (sqi : ∀ i : Iᵒᵖ,
      ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i))
    [∀ i : Iᵒᵖ, QuasiCompact (ηg.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (ηg.app i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    (Fi : ∀ i : Iᵒᵖ,
      Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (torsionFi : ∀ i : Iᵒᵖ, CategoryTheory.Sheaf.IsTorsion (Fi i))
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map a.op)).obj (Fi (op i)) ⟶ Fi (op j))
    (hφid : ∀ i : I,
      φ (𝟙 i) = eqToHom (congrArg
        (fun a : DT.obj (op i) ⟶ DT.obj (op i) ↦
          (Etale.upperStar AddCommGrpCat.{u + 1} a).obj (Fi (op i)))
        (DT.map_id (op i))) ≫
        (Etale.upperStarId AddCommGrpCat.{u + 1} (DT.obj (op i))).hom.app (Fi (op i)))
    (hφcomp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (Etale.upperStarComp AddCommGrpCat.{u + 1}
        (DT.map b.op) (DT.map a.op) (DT.map (a ≫ b).op)
        (DT.map_comp b.op a.op)).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map b.op)).map (φ a) ≫ φ b)
    (D : I ⥤ Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ιF : ∀ i : I, D.obj i ≅
      (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op i))).obj (Fi (op i)))
    (hD : ∀ {i j : I} (a : i ⟶ j),
      D.map a ≫ (ιF j).hom = (ιF i).hom ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (cT.π.app (op j))
          (DT.map a.op) (cT.π.app (op i)) (cT.w a.op).symm).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op j))).map (φ a))
    (cF : Cocone D) (hcF : IsColimit cF)
    (q : ℕ)
    (hbase : ∀ i : Iᵒᵖ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (DX.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (sqi i).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          (Fi i))))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cF.pt))) := by
  classical
  let F := fun i : I ↦ Fi (op i)
  have hid := hφid
  have hcomp := fun i j k a b ↦ @hφcomp i j k a b
  have hLaws := relativeHigherImage_cone_laws DT DS ηg cT cS g hg F φ hid hcomp
    D ιF (fun i j a ↦ hD a) cF q
  obtain ⟨H, eH, hH, legsH, hlegsH⟩ :=
    presentedDiagramWithLegsOfLaws (relativeHigherImageObj DT DS ηg cS F q)
    (relativeHigherImageMap DT DS ηg cS F φ q) ((higherImageFunctor g q).obj cF.pt)
    (relativeHigherImageLeg DT DS ηg cT cS g hg F D ιF cF q) hLaws
  let cH : Cocone H := ⟨(higherImageFunctor g q).obj cF.pt, legsH⟩
  let legs := cH.ι
  obtain ⟨c0, hc0⟩ := getColimitCocone H
  have hA : ∀ (i j : I) (a : i ⟶ j), D.map a =
      (ιF i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cT.π.app (op j)) (DT.map a.op)
          (cT.π.app (op i)) (cT.w a.op).symm).hom.app (F i) ≫
        ((cT.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (φ a) ≫ (ιF j).inv := by
    intro i j a
    simpa only [F, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun t ↦ t ≫ (ιF j).inv) (hD a)
  have : IsIso (hc0.desc cH) :=
    higherDirectImage_relative_continuity_preorder DT DS ηg cT hcT cS hcS g hg F φ hid hcomp
      D ιF hA cF hcF q H eH
      (by intro i j a; exact hH i j a)
      c0 hc0 legs
      (by intro i; exact hlegsH i)
  have hcH : IsColimit cH :=
    IsColimit.ofPointIso (F := H) (r := c0) (t := cH)
      hc0 (i := ‹IsIso (hc0.desc cH)›)
  let U := (f)^*[AddCommGrpCat.{u + 1}]
  let P := H ⋙ U
  let cP := U.mapCocone cH
  have : PreservesColimitsOfSize.{u, u} U := inverseImage_preservesColimits f
  have hcP : IsColimit cP := isColimitOfPreserves U hcH
  let E := D ⋙ (e)^*[AddCommGrpCat.{u + 1}]
  let cE := ((e)^*[AddCommGrpCat.{u + 1}]).mapCocone cF
  have : PreservesColimitsOfSize.{u, u}
      ((e)^*[AddCommGrpCat.{u + 1}]) := inverseImage_preservesColimits e
  have hcE : IsColimit cE := isColimitOfPreserves _ hcF
  let G := fun i : I ↦ ((ηe.app (op i))^*[AddCommGrpCat.{u + 1}]).obj (F i)
  let ψ : ∀ {i j : I} (a : i ⟶ j),
      ((DY.map a.op)^*[AddCommGrpCat.{u + 1}]).obj (G i) ⟶ G j := fun {i j} a ↦
    (squareUpperStarIso AddCommGrpCat.{u + 1} ⟨ηe.naturality a.op⟩).inv.app (F i) ≫
      ((ηe.app (op j))^*[AddCommGrpCat.{u + 1}]).map (φ a)
  let eE : ∀ i : I, E.obj i ≅
      ((cY.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj (G i) :=
    fun i ↦ ((e)^*[AddCommGrpCat.{u + 1}]).mapIso (ιF i) ≪≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} ⟨he (op i)⟩).app (F i)
  have hidE : ∀ i : I, ψ (𝟙 i) =
      eqToHom (congrArg (fun a : DY.obj (op i) ⟶ DY.obj (op i) ↦
        ((a)^*[AddCommGrpCat.{u + 1}]).obj (G i)) (DY.map_id (op i))) ≫
        (upperStarId AddCommGrpCat.{u + 1} (DY.obj (op i))).hom.app (G i) := by
    intro i
    dsimp only [ψ]
    rw [hid i]
    exact pullback_system_identity_transport (ηe.app (op i)) _ _
      (DT.map_id (op i)) (DY.map_id (op i)) _ (F i)
  have hcompE : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k), ψ (a ≫ b) =
      (upperStarComp AddCommGrpCat.{u + 1} (DY.map b.op) (DY.map a.op)
        (DY.map (a ≫ b).op) (DY.map_comp b.op a.op)).hom.app (G i) ≫
      ((DY.map b.op)^*[AddCommGrpCat.{u + 1}]).map (ψ a) ≫ ψ b := by
    intro i j k a b
    dsimp only [ψ]
    rw [hcomp i j k a b]
    exact pullback_system_composition _ _ _ (DT.map_comp b.op a.op)
      (DY.map_comp b.op a.op) (F i) (F j) (F k) (φ a) (φ b)
  have hmapE : ∀ (i j : I) (a : i ⟶ j), E.map a ≫ (eE j).hom =
      (eE i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cY.π.app (op j)) (DY.map a.op)
          (cY.π.app (op i)) (cY.w a.op).symm).hom.app (G i) ≫
        ((cY.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (ψ a) := by
    intro i j a
    simp only [E, eE, G, ψ, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc]
    exact pullback_coefficient_transition ⟨ηe.naturality a.op⟩ ⟨he (op j)⟩ ⟨he (op i)⟩
      (cT.w a.op).symm (cY.w a.op).symm (F i) (F j) (φ a) (ιF i) (ιF j) (D.map a)
      (hD a)
  let βi : ∀ i : I,
      ((ηf.app (op i))^*[AddCommGrpCat.{u + 1}]).obj
        ((higherImageFunctor (ηg.app (op i)) q).obj (F i)) ⟶
      (higherImageFunctor (ηh.app (op i)) q).obj (G i) :=
    fun i ↦ abelianHigherExchange (sqi (op i)).toCommSq (F i) q
  have hisoβi : ∀ i : I, IsIso (βi i) := by
    intro i
    exact (abelianHigherExchange_isIso_iff (sqi (op i)).toCommSq (F i) q).2
      (hbase (op i))
  let eP : ∀ i : I, P.obj i ≅
      ((cX.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj
        (((ηf.app (op i))^*[AddCommGrpCat.{u + 1}]).obj
          ((higherImageFunctor (ηg.app (op i)) q).obj (F i))) :=
    fun i ↦ U.mapIso (eH i) ≪≫
    (squareUpperStarIso AddCommGrpCat.{u + 1} ⟨hf (op i)⟩).app
      ((higherImageFunctor (ηg.app (op i)) q).obj (F i))
  let eB : ∀ i : I, P.obj i ≅
      ((cX.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj
        ((higherImageFunctor (ηh.app (op i)) q).obj (G i)) :=
    fun i ↦ eP i ≪≫
    ((cX.π.app (op i))^*[AddCommGrpCat.{u + 1}]).mapIso (@asIso _ _ _ _ (βi i) (hisoβi i))
  let β := abelianHigherExchange sq.toCommSq cF.pt q
  let legsB : P ⟶ (Functor.const I).obj ((higherImageFunctor h q).obj cE.pt) :=
    cP.ι ≫ (Functor.const I).map β
  have hmapB : ∀ (i j : I) (a : i ⟶ j), P.map a =
      (eB i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cX.π.app (op j)) (DX.map a.op)
          (cX.π.app (op i)) (cX.w a.op).symm).hom.app
            ((higherImageFunctor (ηh.app (op i)) q).obj (G i)) ≫
        ((cX.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map
          (relativeHigherImageExchange ⟨ηh.naturality a.op⟩
            (G i) (G j) (ψ a) q) ≫ (eB j).inv := by
    intro i j a
    have hm := pullback_coefficient_transition
      (show CommSq (DX.map a.op) (ηf.app (op j)) (ηf.app (op i))
        (DS.map a.op) from ⟨ηf.naturality a.op⟩)
      (show CommSq (cX.π.app (op j)) f (ηf.app (op j))
        (cS.π.app (op j)) from ⟨hf (op j)⟩)
      (show CommSq (cX.π.app (op i)) f (ηf.app (op i))
        (cS.π.app (op i)) from ⟨hf (op i)⟩)
      (cS.w a.op).symm (cX.w a.op).symm
      ((higherImageFunctor (ηg.app (op i)) q).obj (F i))
      ((higherImageFunctor (ηg.app (op j)) q).obj (F j))
      (relativeHigherImageExchange ⟨ηg.naturality a.op⟩ (F i) (F j) (φ a) q)
      (eH i) (eH j) (H.map a) (by
        rw [hH i j a]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)
    have hcube := relativeExchange_cube (sqi (op i)) (sqi (op j))
      ⟨ηf.naturality a.op⟩ ⟨ηg.naturality a.op⟩
      ⟨ηh.naturality a.op⟩ ⟨ηe.naturality a.op⟩ (F i) (F j) (φ a) q
    have ht := coefficient_square_transport
      ((cX.π.app (op i))^*[AddCommGrpCat.{u + 1}])
      ((DX.map a.op)^*[AddCommGrpCat.{u + 1}])
      ((cX.π.app (op j))^*[AddCommGrpCat.{u + 1}])
      (upperStarComp AddCommGrpCat.{u + 1} (cX.π.app (op j)) (DX.map a.op)
        (cX.π.app (op i)) (cX.w a.op).symm).hom
      (βi i) (βi j)
      ((squareUpperStarIso AddCommGrpCat.{u + 1} ⟨ηf.naturality a.op⟩).inv.app
          ((higherImageFunctor (ηg.app (op i)) q).obj (F i)) ≫
        ((ηf.app (op j))^*[AddCommGrpCat.{u + 1}]).map
          (relativeHigherImageExchange ⟨ηg.naturality a.op⟩ (F i) (F j) (φ a) q))
      (relativeHigherImageExchange ⟨ηh.naturality a.op⟩ (G i) (G j) (ψ a) q)
      (by simpa only [βi, G, ψ, higherImageFunctor, Functor.comp_obj, Category.assoc] using hcube)
      (eP i).hom (eP j).hom (P.map a) (by
        simpa only [eP, P, U, Functor.comp_map, Functor.comp_obj, Iso.trans_hom,
          Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hm)
    apply map_eq_of_comparison (eB i) (eB j) (P.map a)
      ((upperStarComp AddCommGrpCat.{u + 1} (cX.π.app (op j)) (DX.map a.op)
        (cX.π.app (op i)) (cX.w a.op).symm).hom.app
          ((higherImageFunctor (ηh.app (op i)) q).obj (G i)))
      (((cX.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map
        (relativeHigherImageExchange ⟨ηh.naturality a.op⟩ (G i) (G j) (ψ a) q))
    simpa only [eB, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      Category.assoc] using ht
  have hlegsB : ∀ i : I, legsB.app i = (eB i).hom ≫
      relativeHigherImageExchange ⟨hh (op i)⟩ (G i) cE.pt
        ((eE i).inv ≫ cE.ι.app i) q := by
    intro i
    have hcube := relativeExchange_cube (sqi (op i)) sq
      ⟨hf (op i)⟩ ⟨hg (op i)⟩ ⟨hh (op i)⟩ ⟨he (op i)⟩
      (F i) cF.pt ((ιF i).inv ≫ cF.ι.app i) q
    have coeff : (eE i).inv ≫ cE.ι.app i =
        (squareUpperStarIso AddCommGrpCat.{u + 1} ⟨he (op i)⟩).inv.app (F i) ≫
          ((e)^*[AddCommGrpCat.{u + 1}]).map ((ιF i).inv ≫ cF.ι.app i) := by
      simp only [eE, cE, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
        Functor.mapCocone_ι_app, Functor.map_comp, Category.assoc]
    rw [coeff]
    have hc := congrArg (fun z ↦
      (squareUpperStarIso AddCommGrpCat.{u + 1} ⟨hf (op i)⟩).hom.app
        ((higherImageFunctor (ηg.app (op i)) q).obj (F i)) ≫ z) hcube
    have hr := congrArg (fun z ↦ U.map (eH i).hom ≫ z) hc
    simpa only [legsB, NatTrans.comp_app, Functor.const_map_app, cP, cH,
      Functor.mapCocone_ι_app, hlegsH, relativeHigherImageLeg, eB, eP, βi, β, U, G, cE,
      Functor.mapCocone_pt, higherImageFunctor, Functor.comp_obj, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc] using hr
  have : ∀ i : Iᵒᵖ, QuasiCompact (ηh.app i) := fun i ↦ by
    rw [← (sqi i).hom_snd]
    infer_instance
  have : ∀ i : Iᵒᵖ, QuasiSeparated (ηh.app i) := fun i ↦ by
    rw [← (sqi i).hom_snd]
    infer_instance
  have hmapE' : ∀ (i j : I) (a : i ⟶ j), E.map a =
      (eE i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cY.π.app (op j)) (DY.map a.op)
          (cY.π.app (op i)) (cY.w a.op).symm).hom.app (G i) ≫
        ((cY.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (ψ a) ≫ (eE j).inv := by
    intro i j a
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun t ↦ t ≫ (eE j).inv) (hmapE i j a)
  have := higherDirectImage_relative_continuity_preorder DY DX ηh cY hcY cX hcX h hh G ψ
    hidE hcompE E eE hmapE' cE hcE q P eB hmapB cP hcP legsB hlegsB
  have : IsIso β := isIso_of_isIso_colimit_comparison cP hcP β this
  exact (abelianHigherExchange_isIso_iff sq.toCommSq cF.pt q).1 ‹IsIso β›

end AlgebraicGeometry
