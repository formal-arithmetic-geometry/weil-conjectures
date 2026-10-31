/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! Composition of semilinear return morphisms. -/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

/-- Naturality combines the exchange and point cocycles into a return cocycle.
Source: compact-return power-law argument, naturality step.
(blueprint: lem-fd-compact-return-composition).

Proof: substitute the exchange cocycle and the point cocycle. Naturality of the
second exchange moves the first structure map to the left. Naturality of the
second point trivialization then moves the whole first return to the left. -/
theorem compact_return_composition
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    (P₁ P₂ P₁₂ : C ⥤ C) (Q₁ Q₂ Q₁₂ : D ⥤ D)
    (cP : P₁₂ ≅ P₁ ⋙ P₂) (cQ : Q₁₂ ≅ Q₁ ⋙ Q₂)
    (e₁ : T ⋙ Q₁ ⟶ P₁ ⋙ T) (e₂ : T ⋙ Q₂ ⟶ P₂ ⋙ T)
    (e₁₂ : T ⋙ Q₁₂ ⟶ P₁₂ ⋙ T)
    (r₁ : Q₁ ≅ 𝟭 D) (r₂ : Q₂ ≅ 𝟭 D) (r₁₂ : Q₁₂ ≅ 𝟭 D)
    (he : ∀ K, (cQ.hom.app (T.obj K)) ≫ Q₂.map (e₁.app K) ≫
      e₂.app (P₁.obj K) = e₁₂.app K ≫ T.map (cP.hom.app K))
    (hr : ∀ N, r₁₂.inv.app N ≫ cQ.hom.app N =
      r₂.inv.app N ≫ Q₂.map (r₁.inv.app N))
    (K : C) (θ₁ : P₁.obj K ⟶ K) (θ₂ : P₂.obj K ⟶ K) :
    r₁₂.inv.app (T.obj K) ≫ e₁₂.app K ≫
        T.map (cP.hom.app K ≫ P₂.map θ₁ ≫ θ₂) =
      (r₁.inv.app (T.obj K) ≫ e₁.app K ≫ T.map θ₁) ≫
        (r₂.inv.app (T.obj K) ≫ e₂.app K ≫ T.map θ₂) := by
  have hn := e₂.naturality θ₁
  have ht := r₂.inv.naturality
    (r₁.inv.app (T.obj K) ≫ e₁.app K ≫ T.map θ₁)
  simp only [Functor.comp_map, Functor.id_map] at hn ht
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (he K), reassoc_of% (hr (T.obj K)), ← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [← reassoc_of% ht]

end
