/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Derived complete complexes with perfect reduction are perfect

Let `R` be a Noetherian ring and `ϖ ∈ R` a nonzerodivisor in the Jacobson radical. A complex
`C ∈ D(R)` which is derived `ϖ`-complete, in the sense that it receives no nonzero morphism from
an object on which `ϖ` acts invertibly, and whose reduction `C ⊗ᴸ R/ϖ = cone(ϖ : C ⟶ C)` is
perfect, is itself perfect (Stacks, Tag 0CQG). This is the algebraic input of the integral stage
of `sk-lem-finite` (Step 2 of the proof of `thm-pod-point-perfectness`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- A derived `ϖ`-complete complex whose reduction modulo `ϖ` is perfect is perfect, for `ϖ` a
nonzerodivisor in the Jacobson radical of a Noetherian ring. The reduction is the third vertex of
a distinguished triangle `C ──ϖ──▶ C ⟶ C₁ ⟶ C⟦1⟧`. -/
theorem isPerfect_of_rightOrthogonal_of_isPerfect_obj₃ [IsNoetherianRing R] {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hJ : ϖ ∈ (⊥ : Ideal R).jacobson)
    {C C₁ : DerivedCategory (ModuleCat.{u} R)} {g : C ⟶ C₁} {h : C₁ ⟶ C⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (ϖ • 𝟙 C) g h ∈ distTriang _)
    (hC : ∀ (L : DerivedCategory (ModuleCat.{u} R)) (f : L ⟶ C), IsIso (ϖ • 𝟙 L) → f = 0)
    (hC₁ : C₁.IsPerfect) : C.IsPerfect :=
  sorry

end DerivedCategory
