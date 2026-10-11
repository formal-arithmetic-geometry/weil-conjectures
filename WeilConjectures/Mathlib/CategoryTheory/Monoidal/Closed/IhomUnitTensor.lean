/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The comparison `[A, 𝟙] ⊗ Z ⟶ [A, Z]` along a monoidal functor

For a monoidal functor `G` between monoidal closed categories, the internal hom comparison
`G [A, B] ⟶ [G A, G B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) intertwines the
canonical maps `[A, 𝟙] ⊗ Z ⟶ [A, Z]` (`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`) for
`A` and for `G A`: `CategoryTheory.Functor.Monoidal.ihomComparison_ihomUnitTensorToIhom`.
-/

@[expose] public section

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory MonoidalClosed LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]

/-- The internal hom comparison of a monoidal functor `G` intertwines the canonical maps
`[A, 𝟙] ⊗ Z ⟶ [A, Z]` for `A` and `G A`:
```
  G [A, 𝟙] ⊗ G Z ──────μ──────▶ G ([A, 𝟙] ⊗ Z) ──G φ──▶ G [A, Z]
        │                                                  │
        ▼                                                  ▼
  [G A, 𝟙] ⊗ G Z ─────────────────φ───────────────▶ [G A, G Z]
```
-/
lemma ihomComparison_ihomUnitTensorToIhom (A Z : C) :
    μ G _ Z ≫ G.map (ihomUnitTensorToIhom A Z) ≫ (ihomComparison G A).natTrans.app Z =
      (((ihomComparison G A).natTrans.app (𝟙_ C) ≫ (ihom (G.obj A)).map (η G)) ▷ G.obj Z) ≫
        ihomUnitTensorToIhom (G.obj A) (G.obj Z) := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq]
  simp only [ihomUnitTensorToIhom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ihomComparison_ev, whiskerLeft_curry_ihom_ev_app, μ_natural_right_assoc]
  have hl : μ G (𝟙_ C) Z ≫ G.map (λ_ Z).hom = η G ▷ G.obj Z ≫ (λ_ _).hom := by
    rw [LaxMonoidal.left_unitality G, ← comp_whiskerRight_assoc, Monoidal.η_ε, id_whiskerRight,
      Category.id_comp]
  rw [← G.map_comp, whiskerLeft_curry_ihom_ev_app, G.map_comp, G.map_comp,
    LaxMonoidal.associativity_inv_assoc, ← μ_natural_left_assoc]
  erw [hl]
  rw [associator_inv_naturality_middle_assoc, MonoidalCategory.whiskerLeft_comp]
  have hR : (G.obj A ◁ (ihomComparison G A).natTrans.app (𝟙_ C) ≫
      G.obj A ◁ (ihom (G.obj A)).map (η G)) ≫ (ihom.ev (G.obj A)).app (𝟙_ D) =
      (μ G A ((ihom A).obj (𝟙_ C)) ≫ G.map ((ihom.ev A).app (𝟙_ C))) ≫ η G := by
    rw [Category.assoc, ihom.ev_naturality, ihomComparison_ev_assoc, Category.assoc]
  rw [← comp_whiskerRight_assoc _ (η G), ← comp_whiskerRight_assoc _ ((ihom.ev _).app _), hR]
  simp only [comp_whiskerRight, Category.assoc]
  rfl

end CategoryTheory.Functor.Monoidal
