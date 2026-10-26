/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# The regular module corepresents global sections

* `CategoryTheory.Functor.CorepresentableBy.ofBijective`: if `a : U ⟶ F' X` is such that
  `f ↦ a ≫ F' f` is bijective on morphisms out of `X`, then `X` corepresents
  `Y ↦ (U ⟶ F' Y)`.
* `CategoryTheory.Mod.bijective_comp_map_regular`: let `Φ : Mod_A ⥤ D` be an equivalence and
  `F' : D ⥤ C` a functor with `Φ ⋙ F' ≅ forget`. Then `Φ A` corepresents
  `Y ↦ (𝟙 ⟶ F' Y)`, through the unit `1 : 𝟙 ⟶ A`: morphisms of `A`-modules out of `A` are the
  global sections of the target.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj Opposite

namespace CategoryTheory

/-- If `f ↦ a ≫ F' f` is a bijection from the morphisms out of `X` for every target, then `X`
corepresents `Y ↦ (U ⟶ F' Y)`. -/
noncomputable def Functor.CorepresentableBy.ofBijective {D C' : Type*} [Category* D]
    [Category* C']
    (F' : D ⥤ C') {U : C'} {X : D} (a : U ⟶ F'.obj X)
    (h : ∀ Y : D, Function.Bijective (fun f : X ⟶ Y ↦ a ≫ F'.map f)) :
    (F' ⋙ coyoneda.obj (op U)).CorepresentableBy X where
  homEquiv {Y} := Equiv.ofBijective _ (h Y)
  homEquiv_comp g f := by simp

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] {A : C} [MonObj A] {D : Type*}
  [Category* D]

/-- Let `Φ : Mod_A ⥤ D` be fully faithful and essentially surjective and `F' : D ⥤ C` with
`Φ ⋙ F' ≅ forget`. Then morphisms `Φ A ⟶ Y` are the morphisms `𝟙 ⟶ F' Y`, through the unit
section of `A`. -/
lemma bijective_comp_map_regular (Φ : Mod C A ⥤ D) [Φ.Full] [Φ.Faithful] [Φ.EssSurj]
    (F' : D ⥤ C) (τ : Φ ⋙ F' ≅ Mod.forget A) (Y : D) :
    Function.Bijective
      (fun f : Φ.obj (regular A) ⟶ Y ↦ (η[A] ≫ τ.inv.app (regular A)) ≫ F'.map f) := by
  let e := Φ.objObjPreimageIso Y
  have key (x : regular A ⟶ Φ.objPreimage Y) :
      (η[A] ≫ τ.inv.app (regular A)) ≫ F'.map (Φ.map x ≫ e.hom) =
        (η[A] ≫ x.hom) ≫ τ.inv.app _ ≫ F'.map e.hom := by
    have nat := τ.inv.naturality x
    dsimp only [Functor.comp_map, Mod.forget_map] at nat
    rw [Functor.map_comp, Category.assoc, ← reassoc_of% nat, Category.assoc]
    rfl
  have hf (f : Φ.obj (regular A) ⟶ Y) : f = Φ.map (Φ.preimage (f ≫ e.inv)) ≫ e.hom := by
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨fun f f' h ↦ ?_, fun s ↦ ?_⟩
  · dsimp only at h
    rw [hf f, hf f', key, key] at h
    rw [hf f, hf f', regular_hom_ext ((cancel_mono _).1 h)]
  · refine ⟨Φ.map (regularLift _ (s ≫ F'.map e.inv ≫ τ.hom.app _)) ≫ e.hom, ?_⟩
    dsimp only
    rw [key, one_comp_regularLift, Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

end Mod

end CategoryTheory
