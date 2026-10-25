/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction

/-!

# Naturality of the exchange restriction

The exchange restriction `ι^* c^! P ⟶ d^! Δ^* P` of a base-change square
(`CategoryTheory.Adjunction.exchangeRestriction`) is natural in `P`.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

namespace CategoryTheory

variable {C₂ : Type u₁} {CC : Type u₂} {CF : Type u₃} {CX : Type u₄}
  [Category.{v₁} C₂] [Category.{v₂} CC] [Category.{v₃} CF] [Category.{v₄} CX]
  {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR) {dL : CF ⥤ CX} {dR : CX ⥤ CF}
  (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX) (σ : cL ⋙ Δ ≅ ι ⋙ dL)

/-- **Naturality of the exchange restriction** `ι^* c^! P ⟶ d^! Δ^* P` in `P`. -/
@[reassoc]
lemma Adjunction.exchangeRestriction_naturality {P P' : C₂} (f : P ⟶ P') :
    a.exchangeRestriction g ι Δ σ P ≫ dR.map (Δ.map f) =
      ι.map (cR.map f) ≫ a.exchangeRestriction g ι Δ σ P' := by
  simp only [Adjunction.exchangeRestriction, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_left, Category.assoc, ← Functor.map_comp]
  congr 1
  have h := σ.inv.naturality (cR.map f)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  rw [reassoc_of% h, ← Functor.map_comp, Adjunction.counit_naturality]

end CategoryTheory
