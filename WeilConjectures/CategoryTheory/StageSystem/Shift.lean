/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive

/-!
# Shifts on the pair category of a stage system

Let `S` be a stage system whose stages `C i` carry shifts by `ℤ`, whose transition functors
commute with the shifts and whose associators are compatible with these commutations. The shift
functors of the stages then form, for every `a : ℤ`, a morphism of stage systems
`CategoryTheory.StageSystem.shiftMorphism S a : S.Morphism S`, and the induced functors on the
pair category `S.PairCategory` (the filtered `2`-colimit of the stages) are the shift functors of
a shift by `ℤ` on it (`CategoryTheory.StageSystem.PairCategory.hasShift`): `(i, x)⟦a⟧ = (i, x⟦a⟧)`.
The stage inclusions commute with the shifts, and so do the identifications `j_j ∘ T ≅ j_i`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, HasShift (C i) ℤ] (S : StageSystem C) [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]

/-- The shift functors by `a` of the stages, as a morphism of stage systems. -/
noncomputable def shiftMorphism (a : ℤ) : Morphism S S where
  Φ i := shiftFunctor (C i) a
  β h := (S.T h).commShiftIso a
  coh h h' x := by
    have := NatTrans.shift_app_comm (S.assoc h h').hom a x
    simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at this
    exact this

lemma shiftMorphism_Φ (a : ℤ) (i : I) : (S.shiftMorphism a).Φ i = shiftFunctor (C i) a := rfl

lemma shiftMorphism_β (a : ℤ) {i j : I} (h : i ≤ j) :
    (S.shiftMorphism a).β h = (S.T h).commShiftIso a := rfl

/-- A compatible family of isomorphisms can be inverted. -/
@[simps]
def _root_.CategoryTheory.StageSystem.Morphism.Hom.invOfIso {D : I → Type*}
    [∀ i, Category (D i)] {S₁ : StageSystem D} {S₂ : StageSystem C}
    {F G : Morphism S₁ S₂} (τ : Morphism.Hom F G) (e : ∀ i, F.Φ i ≅ G.Φ i)
    (he : ∀ i, (e i).hom = τ.τ i) : Morphism.Hom G F where
  τ i := (e i).inv
  comm h x := by
    have := τ.comm h x
    rw [← he, ← he] at this
    rw [← cancel_epi ((S₂.T h).map ((e _).hom.app x)), ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Functor.map_id, Category.id_comp, reassoc_of% this,
      Iso.hom_inv_id_app, Category.comp_id]

/-- The isomorphisms `x⟦0⟧ ≅ x` of the stages, as a compatible family. -/
@[simps]
noncomputable def shiftZeroHom : Morphism.Hom (S.shiftMorphism 0) (Morphism.id S) where
  τ i := (shiftFunctorZero (C i) ℤ).hom
  comm h x := by
    dsimp [shiftMorphism]
    simp only [Morphism.id_β, Iso.refl_hom, NatTrans.id_app, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Category.assoc, Iso.inv_hom_id_app]
    repeat erw [Category.comp_id]

/-- The isomorphisms `x⟦a + b⟧ ≅ x⟦a⟧⟦b⟧` of the stages, as a compatible family. -/
@[simps]
noncomputable def shiftAddHom (a b : ℤ) :
    Morphism.Hom (S.shiftMorphism (a + b)) ((S.shiftMorphism a).comp (S.shiftMorphism b)) where
  τ i := (shiftFunctorAdd (C i) a b).hom
  comm h x := by
    dsimp [shiftMorphism]
    simp only [Morphism.comp_β, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.comp_obj, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.comp_id, Category.id_comp, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]

variable [IsDirectedOrder I]

open PairCategory

/-- The isomorphism `(i, x)⟦0⟧ ≅ (i, x)` of the pair category. -/
noncomputable def shiftZeroIso : (S.shiftMorphism 0).functor ≅ 𝟭 _ :=
  Morphism.descNatIso (S.shiftZeroHom)
    ((S.shiftZeroHom).invOfIso (fun i ↦ shiftFunctorZero (C i) ℤ) (fun _ ↦ rfl))
    (by ext i x; simp [shiftMorphism]) (by ext i x; simp [shiftMorphism]) ≪≫
    Morphism.functorIdIso

/-- The isomorphism `(i, x)⟦a + b⟧ ≅ (i, x)⟦a⟧⟦b⟧` of the pair category. -/
noncomputable def shiftAddIso (a b : ℤ) :
    (S.shiftMorphism (a + b)).functor ≅
      (S.shiftMorphism a).functor ⋙ (S.shiftMorphism b).functor :=
  Morphism.descNatIso (S.shiftAddHom a b)
    ((S.shiftAddHom a b).invOfIso (fun i ↦ shiftFunctorAdd (C i) a b) (fun _ ↦ rfl))
    (by ext i x; simp [shiftMorphism]) (by ext i x; simp [shiftMorphism]) ≪≫
    Morphism.functorCompIso _ _

lemma shiftZeroIso_hom_app (X : S.PairCategory) :
    (S.shiftZeroIso).hom.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).hom.app X.obj) :=
  Category.comp_id _

lemma shiftZeroIso_inv_app (X : S.PairCategory) :
    (S.shiftZeroIso).inv.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).inv.app X.obj) :=
  Category.id_comp _

lemma shiftAddIso_hom_app (a b : ℤ) (X : S.PairCategory) :
    (S.shiftAddIso a b).hom.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).hom.app X.obj) :=
  Category.comp_id _

lemma shiftAddIso_inv_app (a b : ℤ) (X : S.PairCategory) :
    (S.shiftAddIso a b).inv.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).inv.app X.obj) :=
  Category.id_comp _

lemma shift_map_ι (a : ℤ) {i : I} {x y : C i} (f : x ⟶ y) :
    (S.shiftMorphism a).functor.map ((S.ι i).map f) = (S.ι i).map (f⟦a⟧') :=
  Morphism.functor_map_ι _ f

/-- The data of the shift by `ℤ` on the pair category. -/
noncomputable def shiftMkCore : ShiftMkCore S.PairCategory ℤ where
  F a := (S.shiftMorphism a).functor
  zero := S.shiftZeroIso
  add := S.shiftAddIso
  assoc_hom_app a b c X := by
    obtain ⟨i, x⟩ := X
    rw [shiftAddIso_hom_app, shiftAddIso_hom_app, shiftAddIso_hom_app, shiftAddIso_hom_app]
    dsimp only [Morphism.functor_obj, shiftMorphism_Φ]
    erw [shift_map_ι, eqToHom_mk]
    simp only [← Functor.map_comp]
    congr 1
    simpa [shiftFunctorAdd'] using shiftFunctorAdd_assoc_hom_app a b c x
  zero_add_hom_app a X := by
    obtain ⟨i, x⟩ := X
    rw [shiftAddIso_hom_app, shiftZeroIso_inv_app]
    dsimp only [Morphism.functor_obj, shiftMorphism_Φ]
    erw [shift_map_ι, eqToHom_mk]
    simp only [← Functor.map_comp]
    congr 1
    simpa using shiftFunctorAdd_zero_add_hom_app a x
  add_zero_hom_app a X := by
    obtain ⟨i, x⟩ := X
    rw [shiftAddIso_hom_app, shiftZeroIso_inv_app]
    dsimp only [Morphism.functor_obj, shiftMorphism_Φ]
    erw [eqToHom_mk]
    simp only [← Functor.map_comp]
    congr 1
    simpa using shiftFunctorAdd_add_zero_hom_app a x

/-- The shift by `ℤ` on the pair category: `(i, x)⟦a⟧ = (i, x⟦a⟧)`. -/
noncomputable instance PairCategory.hasShift : HasShift S.PairCategory ℤ :=
  hasShiftMk _ _ S.shiftMkCore

lemma shiftFunctor_eq (a : ℤ) : shiftFunctor S.PairCategory a = (S.shiftMorphism a).functor :=
  rfl

lemma shiftFunctorZero_hom_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory ℤ).hom.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).hom.app X.obj) :=
  S.shiftZeroIso_hom_app X

lemma shiftFunctorZero_inv_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory ℤ).inv.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).inv.app X.obj) :=
  S.shiftZeroIso_inv_app X

lemma shiftFunctorAdd_hom_app (a b : ℤ) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).hom.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).hom.app X.obj) :=
  S.shiftAddIso_hom_app a b X

lemma shiftFunctorAdd_inv_app (a b : ℤ) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).inv.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).inv.app X.obj) :=
  S.shiftAddIso_inv_app a b X

lemma shiftFunctor_map_ι (a : ℤ) {i : I} {x y : C i} (f : x ⟶ y) :
    ((S.ι i).map f)⟦a⟧' = (S.ι i).map (f⟦a⟧') :=
  S.shift_map_ι a f

/-- The stage inclusions commute with the shifts. -/
noncomputable instance (i : I) : (S.ι i).CommShift ℤ where
  commShiftIso a := ((S.shiftMorphism a).ιCompFunctorIso i).symm
  commShiftIso_zero := by
    ext x
    rw [Functor.CommShift.isoZero_hom_app, shiftFunctorZero_inv_app]
    erw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rfl
  commShiftIso_add a b := by
    ext x
    rw [Functor.CommShift.isoAdd_hom_app, shiftFunctorAdd_inv_app]
    erw [Functor.map_id, Category.id_comp, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id_app, Functor.map_id]
    rfl

lemma ι_commShiftIso_hom_app (i : I) (a : ℤ) (x : C i) :
    ((S.ι i).commShiftIso a).hom.app x = 𝟙 _ :=
  rfl

lemma ι_commShiftIso_inv_app (i : I) (a : ℤ) (x : C i) :
    ((S.ι i).commShiftIso a).inv.app x = 𝟙 _ :=
  rfl

/-- The identifications `j_j ∘ T_{j/i} ≅ j_i` commute with the shifts. -/
instance {i j : I} (h : i ≤ j) : NatTrans.CommShift (S.transIso h).hom ℤ where
  shift_comm a := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app]
    rw [ι_commShiftIso_hom_app, ι_commShiftIso_hom_app, transIso_hom_app_eq,
      transIso_hom_app_eq]
    erw [Category.comp_id, Category.comp_id, Morphism.functor_map_mkHom]
    rw [ι_map_eq le_rfl]
    erw [mkHom_comp_mkHom]
    congr 1
    simp only [Morphism.mapAt]
    erw [reassoc_of% ((S.shiftMorphism a).coh h le_rfl x), Iso.hom_inv_id_app]
    exact Category.comp_id _

end StageSystem

end CategoryTheory
