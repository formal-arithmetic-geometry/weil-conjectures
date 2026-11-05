/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import WeilConjectures.CategoryTheory.Adjunction.FullyFaithfulCounitLocal
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso

/-! # Transport of the open projection formula through an adjunction square

The unit calculation is the one used by the native open tensor normalization, made available
for other geometric realizations.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

/-- Compatibility of the unit with the specified open pushforward and pullback squares. -/
def compactProjectionOpen_unitSquare
    {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R') : Prop :=
  ∀ X, FA.map (adj.unit.app X) ≫ eR.hom.app (E.obj X) ≫
    R'.map (eE.hom.app X) = adj'.unit.app (FA.obj X)

/-- The unit square identifies the adjunction transposes after realization. -/
theorem compactProjectionOpen_forget_homEquiv
    {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (hu : compactProjectionOpen_unitSquare adj adj' FA FB eE eR)
    (X : A) (Y : B) (f : E.obj X ⟶ Y) :
    adj'.homEquiv _ _ (eE.inv.app X ≫ FB.map f) =
      FA.map (adj.homEquiv _ _ f) ≫ eR.hom.app Y := by
  rw [adj'.homEquiv_unit, ← hu X, adj.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R'.map_comp_assoc]
  rw [Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Functor.map_id, Category.id_comp]
  exact congrArg (fun z ↦ FA.map (adj.unit.app X) ≫ z) (eR.hom.naturality f).symm

/-- The canonical unit normalization determines the forward open projection square. -/
theorem compactProjectionOpen_forget_of_unit_at
    {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B']
    {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (FA : A ⥤ A') (FB : B ⥤ B')
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {TA' : A' × A' ⥤ A'} {TB' : B' × B' ⥤ B'}
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (rho' : TB' ⋙ R' ≅ R'.prod R' ⋙ TA')
    (M : A) (N : B)
    (gamma : TB.obj (E.obj M, N) ≅ E.obj (TA.obj (M, R.obj N)))
    (gamma' : TB'.obj (E'.obj (FA.obj M), FB.obj N) ≅
      E'.obj (TA'.obj (FA.obj M, R'.obj (FB.obj N))))
    (hu : compactProjectionOpen_unitSquare adj adj' FA FB eE eR)
    (hr : ∀ M N,
      FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) ≫
        TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) =
      eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
        rho'.hom.app (FB.obj M, FB.obj N))
    (hg : adj.homEquiv _ _ gamma.inv =
      TA.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ rho.inv.app (E.obj M, N))
    (hg' : adj'.homEquiv _ _ gamma'.inv =
      TA'.map (Prod.mkHom (adj'.unit.app (FA.obj M)) (𝟙 _)) ≫
        rho'.inv.app (E'.obj (FA.obj M), FB.obj N)) :
    FB.map gamma.hom ≫ eE.hom.app (TA.obj (M, R.obj N)) ≫
        E'.map (tA.hom.app (M, R.obj N) ≫ TA'.map (Prod.mkHom (𝟙 _) (eR.hom.app N))) =
      tB.hom.app (E.obj M, N) ≫ TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 _)) ≫
        gamma'.hom := by
  have hrinv (M N : B) :
      FA.map (rho.inv.app (M, N)) ≫ eR.hom.app (TB.obj (M, N)) ≫
        R'.map (tB.hom.app (M, N)) =
      tA.hom.app (R.obj M, R.obj N) ≫
        TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) ≫
          rho'.inv.app (FB.obj M, FB.obj N) := by
    apply (cancel_mono (rho'.hom.app (FB.obj M, FB.obj N))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hr M N]
    simp only [← FA.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simp only [Functor.comp_obj, Functor.prod_obj, Category.comp_id]
  let X := TA.obj (M, R.obj N)
  let q := tA.hom.app (M, R.obj N) ≫ TA'.map (Prod.mkHom (𝟙 _) (eR.hom.app N))
  let p := tB.hom.app (E.obj M, N) ≫ TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 _))
  have hn : FA.map (TA.map (Prod.mkHom (adj.unit.app M) (𝟙 (R.obj N)))) ≫
      tA.hom.app (R.obj (E.obj M), R.obj N) =
      tA.hom.app (M, R.obj N) ≫
        TA'.map (Prod.mkHom (FA.map (adj.unit.app M)) (𝟙 _)) := by
    simpa using tA.hom.naturality (Prod.mkHom (adj.unit.app M) (𝟙 (R.obj N)))
  have hrn : rho'.inv.app (FB.obj (E.obj M), FB.obj N) ≫
      R'.map (TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 (FB.obj N)))) =
      TA'.map (Prod.mkHom (R'.map (eE.hom.app M)) (𝟙 _)) ≫
        rho'.inv.app (E'.obj (FA.obj M), FB.obj N) := by
    simpa using (rho'.inv.naturality
      (Prod.mkHom (eE.hom.app M) (𝟙 (FB.obj N)))).symm
  have hi : eE.inv.app X ≫ FB.map (gamma.inv) ≫ p =
      E'.map q ≫ gamma'.inv := by
    apply (adj'.homEquiv _ _).injective
    rw [← Category.assoc (eE.inv.app X), adj'.homEquiv_naturality_right,
      compactProjectionOpen_forget_homEquiv adj adj' FA FB eE eR hu]
    dsimp only [X, Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
    rw [hg, adj'.homEquiv_naturality_left, hg']
    dsimp only [p, q]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hrinv (E.obj M) N, hrn, reassoc_of% hn]
    simp only [← TA'.map_comp_assoc]
    congr 2
    apply congrArg TA'.map
    ext <;> simp [hu M]
  have hi' : FB.map (gamma.inv) ≫ p =
      eE.hom.app X ≫ E'.map q ≫ gamma'.inv := by
    calc
      _ = eE.hom.app X ≫ (eE.inv.app X ≫ FB.map (gamma.inv) ≫ p) := by
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      _ = _ := by rw [hi]
  simp only [Functor.map_comp]
  apply (cancel_epi (FB.map (gamma.inv))).1
  simp only [← FB.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  have hi'' := congrArg
    (fun z ↦ z ≫ gamma'.hom) hi'
  simp only [p, q, X, Functor.map_comp, Category.assoc, Iso.inv_hom_id,
    Functor.comp_obj, Functor.prod_obj, Category.comp_id] at hi''
  exact hi''.symm


section InverseMate

variable {A B A' B' : Type*} [Category* A] [Category* B]
  [Category* A'] [Category* B']
  {E : A ⥤ B} {R : B ⥤ A} {E' : A' ⥤ B'} {R' : B' ⥤ A'}
  (adj : E ⊣ R) (adj' : E' ⊣ R') {FA : A ⥤ A'} {FB : B ⥤ B'}
  (eR : R ⋙ FA ≅ FB ⋙ R')

/-- An invertible restriction square gives an invertible extension square if both extensions
are fully faithful and forgetting carries extensions into extensions. -/
theorem isIso_inverseMate_of_extension_image
    [IsIso adj.unit] [IsIso adj'.unit] (M : A) (N : A') (e : FB.obj (E.obj M) ≅ E'.obj N) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ eR.hom)).app M) := by
  have : IsIso (adj'.counit.app (E'.obj N)) :=
    adj'.isIso_counit_app_obj_of_isIso_unit_app N
  have : IsIso (adj'.counit.app (FB.obj (E.obj M))) :=
    adj'.isIso_counit_app_of_iso' e.symm
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Functor.id_obj, Functor.comp_obj, Category.id_comp, Category.comp_id]
  infer_instance

/-- The inverse mate satisfies the open unit square by construction. -/
theorem compactProjectionOpen_unitSquare_of_inverseMate
    [IsIso ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans] :
    compactProjectionOpen_unitSquare adj adj' FA FB
      (asIso ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans).symm eR := by
  intro M
  let e := asIso ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans
  change FA.map (adj.unit.app M) ≫ eR.hom.app (E.obj M) ≫ R'.map (e.inv.app M) = _
  have h := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ eR.hom) M
  rw [← Category.assoc, h, Category.assoc, ← R'.map_comp]
  change adj'.unit.app (FA.obj M) ≫ R'.map (e.hom.app M ≫ e.inv.app M) = _
  simp only [Iso.hom_inv_id_app, Functor.comp_obj]
  rw [R'.map_id, Category.comp_id]

end InverseMate

end CategoryTheory
