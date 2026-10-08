/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Detecting isomorphisms on shifted test objects

A morphism `f : X ⟶ Y` in a category with a shift by an additive group `A` is an isomorphism as
soon as composition with `f` is bijective on morphisms out of every shifted object `Z⟦n⟧`, for a
fixed `n : A`: every object is isomorphic to a shifted one.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {A : Type*} [AddGroup A] [HasShift C A]

/-- A morphism `f : X ⟶ Y` is an isomorphism if, for a fixed `n : A`, composition with `f` is a
bijection `(Z⟦n⟧ ⟶ X) → (Z⟦n⟧ ⟶ Y)` for every object `Z`. -/
lemma isIso_of_bijective_shift_comp {X Y : C} (f : X ⟶ Y) (n : A)
    (hf : ∀ Z : C, Function.Bijective (fun t : Z⟦n⟧ ⟶ X ↦ t ≫ f)) : IsIso f := by
  refine isIso_of_yoneda_map_bijective f fun Z ↦ ?_
  let i : (Z⟦-n⟧)⟦n⟧ ≅ Z := (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).app Z
  have h : (fun t : Z ⟶ X ↦ t ≫ f) =
      (fun s ↦ i.inv ≫ s) ∘ (fun t : (Z⟦-n⟧)⟦n⟧ ⟶ X ↦ t ≫ f) ∘ (fun t ↦ i.hom ≫ t) := by
    ext t
    simp
  rw [h]
  exact (i.homFromEquiv (Z := Y)).bijective.comp
    ((hf _).comp (i.homFromEquiv (Z := X)).symm.bijective)

end CategoryTheory
