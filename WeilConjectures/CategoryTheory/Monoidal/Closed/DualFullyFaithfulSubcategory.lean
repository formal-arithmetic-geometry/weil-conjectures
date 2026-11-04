/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Subcategory

/-!
# Fully faithful duals on full monoidal closed subcategories

For `D = [-, W]`, the bijectivity of `f ↦ D f` only depends on `W` up to isomorphism
(`CategoryTheory.MonoidalClosed.bijective_pre_app_of_iso_right`). If `P` is a monoidal closed
property of objects, braided, and the double-dual maps `A ⟶ D D A` of `P` relative to `W` are
isomorphisms, then `f ↦ D f` is bijective on morphisms between objects of `P` in the ambient
category (`CategoryTheory.ObjectProperty.bijective_pre_app_of_isIso`): this is how Verdier
biduality on `Dᵇc` is read in the ambient derived category.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- The bijectivity of `f ↦ [f, W] : (X ⟶ Y) → ([Y, W] ⟶ [X, W])` only depends on `W` up to
isomorphism. -/
lemma bijective_pre_app_of_iso_right {W W' : C} (e : W ≅ W') (X Y : C)
    (h : Function.Bijective (fun f : X ⟶ Y ↦ (pre f).app W)) :
    Function.Bijective (fun f : X ⟶ Y ↦ (pre f).app W') := by
  have : (fun f : X ⟶ Y ↦ (pre f).app W') =
      (((ihom Y).mapIso e).homCongr ((ihom X).mapIso e)) ∘ (fun f : X ⟶ Y ↦ (pre f).app W) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Functor.mapIso_hom, Functor.mapIso_inv]
    rw [← Category.assoc]
    erw [(pre f).naturality e.inv]
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id,
      Category.comp_id]
  rw [this]
  exact (Iso.homCongr _ _).bijective.comp h

end MonoidalClosed

namespace ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed] [BraidedCategory P.FullSubcategory]

/-- If the double-dual map of `Y` relative to `W` is an isomorphism in the full monoidal closed
subcategory `P`, then `f ↦ [f, W] : (X ⟶ Y) → ([Y, W] ⟶ [X, W])` is bijective in the ambient
category, for `X` in `P`. -/
lemma bijective_pre_app_of_isIso (W : P.FullSubcategory) {X Y : C} (hX : P X) (hY : P Y)
    [IsIso (MonoidalClosed.toIhomIhom W ⟨Y, hY⟩)] :
    Function.Bijective (fun f : X ⟶ Y ↦ (MonoidalClosed.pre f).app W.obj) := by
  have h := MonoidalClosed.bijective_pre_app_of_isIso W ⟨X, hX⟩ ⟨Y, hY⟩
  let FF := P.fullyFaithfulι
  have : (fun f : X ⟶ Y ↦ (MonoidalClosed.pre f).app W.obj) =
      FF.homEquiv ∘ (fun g : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩ ↦
        (MonoidalClosed.pre g).app W) ∘ (FF.homEquiv (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)).symm := by
    funext f
    exact (pre_app_hom ((FF.homEquiv (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)).symm f) W).symm
  rw [this]
  exact FF.homEquiv.bijective.comp (h.comp FF.homEquiv.symm.bijective)

end ObjectProperty

end CategoryTheory
