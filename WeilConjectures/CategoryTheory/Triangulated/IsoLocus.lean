/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The objects at which a natural transformation is an isomorphism

Let `τ : F₁ ⟶ F₂` be a natural transformation between functors `C ⥤ D`. We study the property
`NatTrans.isoLocus τ` of objects `X` such that `τ.app X` is an isomorphism. It is closed under
isomorphisms and stable under retracts. If `C` and `D` are pretriangulated, `F₁` and `F₂` are
triangulated and `τ` commutes with the shifts, then it is a triangulated subcategory: by the
five lemma, a distinguished triangle two of whose objects lie in it has its third object in
it. Being stable under retracts, it is then a *thick* triangulated subcategory.

## Main definitions and results

- `CategoryTheory.NatTrans.isoLocus τ`: the objects `X` such that `τ.app X` is an isomorphism.
- `CategoryTheory.NatTrans.isTriangulated_isoLocus`: it is a triangulated subcategory.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace NatTrans

section

variable {C D : Type*} [Category* C] [Category* D] {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂)

/-- The objects `X` at which the natural transformation `τ` is an isomorphism. -/
def isoLocus : ObjectProperty C := fun X ↦ IsIso (τ.app X)

lemma isoLocus_iff (X : C) : isoLocus τ X ↔ IsIso (τ.app X) := Iff.rfl

instance : (isoLocus τ).IsClosedUnderIsomorphisms where
  of_iso {X Y} e (_ : IsIso (τ.app X)) := by
    change IsIso (τ.app Y)
    have : τ.app Y = F₁.map e.inv ≫ τ.app X ≫ F₂.map e.hom := by
      rw [τ.naturality_assoc, ← F₂.map_comp, e.inv_hom_id, F₂.map_id, comp_id]
    rw [this]
    infer_instance

instance : (isoLocus τ).IsStableUnderRetracts where
  of_retract {X Y} h (_ : IsIso (τ.app Y)) :=
    ⟨F₂.map h.i ≫ inv (τ.app Y) ≫ F₁.map h.r, by
      rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, ← F₁.map_comp, h.retract,
        F₁.map_id], by
      rw [assoc, assoc, τ.naturality, IsIso.inv_hom_id_assoc, ← F₂.map_comp, h.retract,
        F₂.map_id]⟩

end

section Triangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ]

instance [Pretriangulated C] [Pretriangulated D] [F₁.IsTriangulated] [F₂.IsTriangulated] :
    (isoLocus τ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, by
    have h₁ := F₁.map_isZero (isZero_zero C)
    have h₂ := F₂.map_isZero (isZero_zero C)
    exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  isStableUnderShiftBy n := ⟨fun X (_ : IsIso (τ.app X)) ↦ by
    change IsIso (τ.app (X⟦n⟧))
    rw [NatTrans.app_shift τ n X]
    infer_instance⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT (_ : IsIso (τ.app T.obj₁))
      (_ : IsIso (τ.app T.obj₃)) ↦
    show IsIso (τ.app T.obj₂) from
      NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ τ hT inferInstance inferInstance

/-- If `τ : F₁ ⟶ F₂` is a natural transformation between triangulated functors which commutes
with the shifts, the objects at which `τ` is an isomorphism form a triangulated subcategory. -/
lemma isTriangulated_isoLocus [Pretriangulated C] [Pretriangulated D] [F₁.IsTriangulated]
    [F₂.IsTriangulated] : (isoLocus τ).IsTriangulated :=
  inferInstance

end Triangulated

end NatTrans

end CategoryTheory
