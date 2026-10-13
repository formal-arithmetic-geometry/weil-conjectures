/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

/-!

# Mates along equivalences

The mate of an isomorphism is not an isomorphism in general. It is when the two vertical functors
of the square are equivalences: their inverses are right adjoints, so the mate can be taken a
second time, and the iterated mate is the conjugate of the original transformation
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), an isomorphism; since the units and counits
of the equivalences are isomorphisms, this forces the first mate to be an isomorphism.

## Main statements

- `CategoryTheory.isIso_mateEquiv_of_isEquivalence`: for adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and
  equivalences `G` and `H`, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism
  `G ⋙ L₂ ≅ L₁ ⋙ H` is an isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory


variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` is an isomorphism when the vertical functors `G` and `H` are
equivalences. -/
theorem isIso_mateEquiv_of_isEquivalence [G.IsEquivalence] [H.IsEquivalence]
    (α : TwoSquare G L₁ L₂ H) [IsIso α.natTrans] :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  let adj₃ := G.asEquivalence.toAdjunction
  let adj₄ := H.asEquivalence.toAdjunction
  have : IsIso (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).natTrans := by
    rw [iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄]
    exact conjugateEquiv_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α.natTrans
  have (d : D) : IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app d) := by
    have : IsIso (adj₃.unit.app (R₁.obj d)) := by
      simp only [adj₃, Equivalence.toAdjunction_unit]
      infer_instance
    have : IsIso (adj₄.unit.app d) := by
      simp only [adj₄, Equivalence.toAdjunction_unit]
      infer_instance
    have h : G.asEquivalence.inverse.map ((mateEquiv adj₁ adj₂ α).natTrans.app d) =
        inv (adj₃.unit.app (R₁.obj d)) ≫ R₁.map (adj₄.unit.app d) ≫
          (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).natTrans.app (H.obj d) :=
      (IsIso.eq_inv_comp _).mpr (unit_mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) d).symm
    have : IsIso (G.asEquivalence.inverse.map ((mateEquiv adj₁ adj₂ α).natTrans.app d)) := by
      rw [h]
      infer_instance
    exact isIso_of_reflects_iso _ G.asEquivalence.inverse
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory
