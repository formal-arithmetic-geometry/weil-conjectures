/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Mates along fully faithful left adjoints

The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions `L₁ ⊣ R₁`
and `L₂ ⊣ R₂` is not an isomorphism in general. It is when both left adjoints `L₁`, `L₂` are
fully faithful (their units are isomorphisms) and the square of right adjoints commutes up to
*some* natural isomorphism `H ⋙ R₂ ≅ R₁ ⋙ G`
(`CategoryTheory.isIso_mateEquiv_of_isIso_unit`). This applies for instance to the extensions by
zero along open immersions.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` with fully faithful left adjoints is an isomorphism, provided the right
adjoints commute with `G` and `H` up to some natural isomorphism `e : H ⋙ R₂ ≅ R₁ ⋙ G`. Indeed,
at `d`, the mate is the unit of `L₂ ⊣ R₂`, then `R₂` of the isomorphism, then `R₂ H` of the
counit `ε_d` of `L₁ ⊣ R₁`; and `R₂ H ε_d ≅ G R₁ ε_d` (by `e`) is an isomorphism, `R₁ ε_d` being
the inverse of a unit. -/
theorem isIso_mateEquiv_of_isIso_unit [IsIso adj₁.unit] [IsIso adj₂.unit]
    (α : TwoSquare G L₁ L₂ H) [IsIso α.natTrans] (e : H ⋙ R₂ ≅ R₁ ⋙ G) :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  have (d : B) : IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app d) := by
    have : IsIso (R₁.map (adj₁.counit.app d)) := by
      have : IsIso (adj₁.unit.app (R₁.obj d) ≫ R₁.map (adj₁.counit.app d)) := by
        rw [adj₁.right_triangle_components]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adj₁.unit.app (R₁.obj d)) _
    have : IsIso ((H ⋙ R₂).map (adj₁.counit.app d)) :=
      (NatIso.isIso_map_iff e _).mpr (inferInstanceAs (IsIso (G.map (R₁.map _))))
    have : IsIso (R₂.map (H.map (adj₁.counit.app d))) := this
    simp only [mateEquiv_apply, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, rightUnitor_inv_app, leftUnitor_hom_app,
      Functor.comp_map]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp]
    have : IsIso (α.natTrans.app (R₁.obj d)) := inferInstance
    have : IsIso (𝟙 (R₂.obj (H.obj d))) := inferInstance
    exact IsIso.comp_isIso
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory
