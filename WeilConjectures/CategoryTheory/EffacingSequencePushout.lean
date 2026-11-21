/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DeltaFunctor

/-!
# Pushout to an effacing short exact sequence

## References

* Stacks Project, Tag 010T.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

/-- Every short exact sequence maps to an effacing one fixing its left object.

Stacks Project, Tag 010T. -/
theorem effacingSequence_pushout
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    (hF : ∀ (X : A), ∃ (Y : A) (u : X ⟶ Y),
      Mono u ∧ (F.F (n + 1)).map u = 0)
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ (Y : A) (u : S.X₁ ⟶ Y), Mono u ∧ (F.F (n + 1)).map u = 0 ∧
      ∃ p : S ⟶ ShortComplex.cokernelSequence u, p.τ₁ = 𝟙 S.X₁ := by
  obtain ⟨Y, u, hu, hz⟩ := hF S.X₁
  have : Mono u := hu
  have := hS.mono_f
  let w := S.f ≫ pushout.inl S.f u
  have hw : Mono w := inferInstance
  have hw' : w = u ≫ pushout.inr S.f u := pushout.condition
  have hzero : (F.F (n + 1)).map w = 0 := by
    rw [hw', Functor.map_comp, hz, zero_comp]
  have hfzero : S.f ≫ (pushout.inl S.f u ≫ cokernel.π w) = 0 := by
    rw [← Category.assoc]
    exact cokernel.condition w
  have hg := hS.epi_g
  let d := CokernelCofork.IsColimit.desc' hS.exact.gIsCokernel
    (pushout.inl S.f u ≫ cokernel.π w) hfzero
  let p : S ⟶ ShortComplex.cokernelSequence w :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := pushout.inl S.f u
      τ₃ := d.1
      comm₁₂ := by dsimp [w]; simp
      comm₂₃ := d.2.symm }
  exact ⟨_, w, hw, hzero, p, rfl⟩

end CategoryTheory
