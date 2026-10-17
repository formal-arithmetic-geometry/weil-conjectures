/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Morphisms of exact functors

Let `Φ, Ψ : 𝒯 ⥤ 𝒯'` be functors between categories with a shift by `ℤ`, commuting with the shifts
through the isomorphisms `s^Φ : Φ(-[1]) ≅ Φ(-)[1]` and `s^Ψ : Ψ(-[1]) ≅ Ψ(-)[1]`. A *morphism of
exact functors* (blueprint `pur9-def-exact-transformation`) is a natural transformation
`α : Φ ⟶ Ψ` with `s^Ψ_X ∘ α_{X[1]} = α_X[1] ∘ s^Φ_X` for all `X`
(`CategoryTheory.NatTrans.IsExact`). A natural transformation commuting with all the shifts
(`CategoryTheory.NatTrans.CommShift`) is a morphism of exact functors
(`CategoryTheory.NatTrans.isExact_of_commShift`).
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {Φ Ψ : C ⥤ D} [Φ.CommShift ℤ] [Ψ.CommShift ℤ]

namespace NatTrans

/-- Blueprint `pur9-def-exact-transformation`: a natural transformation `α : Φ ⟶ Ψ` of functors
commuting with the shift is a *morphism of exact functors* if it commutes with the
commutation isomorphisms `s^Φ : Φ(-[1]) ≅ Φ(-)[1]` and `s^Ψ : Ψ(-[1]) ≅ Ψ(-)[1]`:
`s^Ψ_X ∘ α_{X[1]} = α_X[1] ∘ s^Φ_X` for all `X`. -/
def IsExact (α : Φ ⟶ Ψ) : Prop :=
  ∀ X : C, α.app (X⟦(1 : ℤ)⟧) ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app X =
    (Φ.commShiftIso (1 : ℤ)).hom.app X ≫ (α.app X)⟦(1 : ℤ)⟧'

/-- A natural transformation commuting with all the shifts is a morphism of exact functors. -/
lemma isExact_of_commShift (α : Φ ⟶ Ψ) [NatTrans.CommShift α ℤ] : α.IsExact :=
  fun X ↦ (NatTrans.shift_app_comm α (1 : ℤ) X).symm

/-- The identity is a morphism of exact functors. -/
lemma isExact_id : NatTrans.IsExact (𝟙 Φ) :=
  isExact_of_commShift _

/-- Morphisms of exact functors are stable under composition. -/
lemma IsExact.comp {Θ : C ⥤ D} [Θ.CommShift ℤ] {α : Φ ⟶ Ψ} {β : Ψ ⟶ Θ} (hα : α.IsExact)
    (hβ : β.IsExact) : (α ≫ β).IsExact := fun X ↦ by
  simp only [NatTrans.comp_app, Category.assoc, hβ X, Functor.map_comp]
  rw [← Category.assoc, hα X, Category.assoc]

end NatTrans

end CategoryTheory
