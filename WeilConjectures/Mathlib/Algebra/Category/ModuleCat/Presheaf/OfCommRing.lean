/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Restriction maps of presheaves of modules over a presheaf of commutative rings

For `M : PresheafOfModulesOfCommRing R`, the restriction map `M.map f` is the abbreviation
`PresheafOfModulesOfCommRing.map`, so the lemmas about `PresheafOfModules.map` do not rewrite it.
We restate the ones we need.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModulesOfCommRing.{v} R)

lemma map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : M.obj U) :
    M.map (i ≫ j) x = M.map j (M.map i x) :=
  PresheafOfModules.map_comp_apply _ _ _ _

lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by
  rw [h]

lemma map_id_apply (X : Cᵒᵖ) (m : M.obj X) : M.map (𝟙 X) m = m := by
  rw [map, PresheafOfModules.map_id]
  rfl

lemma map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X) :
    M.map f (r • m) = R.map f r • M.map f m :=
  PresheafOfModules.map_smul _ _ _ _

end PresheafOfModulesOfCommRing
