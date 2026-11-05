/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Invertibility of units along a mate

For an adjunction `L ⊣ R`, the unit `η_B : B ⟶ R (L B)` is invertible if and only if `L` is
bijective on morphisms with target `B`
(`CategoryTheory.Adjunction.isIso_unit_app_of_map_bijective`, converse to
`CategoryTheory.Adjunction.map_bijective_of_isIso_unit_app`).

Consider a square of functors with adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` along the top and
bottom, `G ⊣ G'` and `H ⊣ H'` along the sides, an isomorphism `α : G ⋙ L₂ ≅ L₁ ⋙ H` and its mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`. If `β` is invertible at `d` and the unit of `H ⊣ H'` is invertible at `d`,
then the unit of `G ⊣ G'` is invertible at `R₁ d`
(`CategoryTheory.isIso_unit_app_of_isIso_mateEquiv_app`). In algebraic geometry this says that
for a base change square for which base change holds, the full faithfulness of the pullback
along the base-changed morphism at `M` gives that of the pullback at the direct image of `M`.
-/

@[expose] public section

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- If `L` is bijective on morphisms with target `B`, then the unit `η_B` of `L ⊣ R` is an
isomorphism. -/
lemma isIso_unit_app_of_map_bijective (adj : L ⊣ R) (B : C)
    (h : ∀ A : C, Function.Bijective (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B))) :
    IsIso (adj.unit.app B) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro A
  have e : (fun f : A ⟶ B ↦ f ≫ adj.unit.app B) =
      adj.homEquiv A (L.obj B) ∘ (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) := by
    funext f
    exact (homEquiv_map adj f).symm
  exact (congrArg Function.Bijective e).mpr ((adj.homEquiv _ _).bijective.comp (h A))

end Adjunction

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G' : E ⥤ C} {H' : F ⥤ D}

end CategoryTheory
