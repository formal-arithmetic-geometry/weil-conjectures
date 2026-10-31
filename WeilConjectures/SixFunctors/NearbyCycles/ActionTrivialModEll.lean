/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.NumberTheory.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!

# Actions which are trivial modulo `ℓ` by `ℓ`-divisible elements

The `ℓ`-adic step of the finiteness of the action of the pro-`p` kernel `P'` on `ℚ̄_ℓ`-nearby
cycles (SGA 4½, [Th. finitude], §3.7): on an object `Y` killed by `ℓ ^ m` (e.g. nearby cycles with
`𝒪_E / ℓ ^ m`-coefficients), an endomorphism which is the identity modulo `ℓ` is of the form
`1 + ℓ g`, hence has order dividing `ℓ ^ m`. So a group in which every element is an `ℓ ^ m`-th
power (e.g. a pro-`p` group, `p ≠ ℓ`) acting on `Y` trivially modulo `ℓ` acts trivially.

## Main results

- `one_add_natCast_mul_pow_eq_one`: in a ring with `ℓ ^ m = 0`, `(1 + ℓ x) ^ (ℓ ^ m) = 1`.
- `CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow`: a group action on `Y` with
  `ℓ ^ m • 𝟙 Y = 0`, trivial after composition with `π : Y ⟶ Z` whose kernel on endomorphisms
  is `ℓ • End Y`, by a group of `ℓ ^ m`-th powers, is trivial.
- `CategoryTheory.Pretriangulated.MonoidHom.eq_one_of_distinguished`: the same when `π` is the
  third vertex of a distinguished triangle `Y ⟶ Y ⟶ Z ⟶ Y⟦1⟧` whose first map is `ℓ • 𝟙 Y`.

-/

@[expose] public section

open CategoryTheory Limits

/-- In a ring in which `ℓ ^ m = 0`, the element `1 + ℓ x` has order dividing `ℓ ^ m`. -/
theorem one_add_natCast_mul_pow_eq_one {R : Type*} [Ring R] {ℓ m : ℕ} (h : (ℓ : R) ^ m = 0)
    (x : R) : (1 + ℓ * x) ^ (ℓ ^ m) = 1 := by
  obtain ⟨q, hq⟩ := dvd_sub_pow_of_dvd_sub (R := Polynomial ℤ) (p := ℓ)
    (a := 1 + (ℓ : Polynomial ℤ) * Polynomial.X) (b := 1) ⟨Polynomial.X, by ring⟩ m
  have := congrArg (Polynomial.aeval x) hq
  simp only [one_pow, map_sub, map_pow, map_add, map_one, map_mul, map_natCast,
    Polynomial.aeval_X] at this
  rw [← sub_eq_zero, this, pow_succ, h, zero_mul, zero_mul]

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Actions trivial modulo `ℓ` by `ℓ`-divisible groups are trivial**: let `Y` be killed by
`ℓ ^ m` and `π : Y ⟶ Z` such that every endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by
`ℓ`. A group in which every element is an `ℓ ^ m`-th power, acting on `Y` by `ρ` with
`ρ τ ≫ π = π` for all `τ`, acts trivially. -/
theorem MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow {Y Z : C} (π : Y ⟶ Z) {ℓ m : ℕ}
    (hℓ : (ℓ ^ m) • 𝟙 Y = 0) (hπ : ∀ f : End Y, f ≫ π = 0 → ∃ g : End Y, f = ℓ • g)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, ρ τ ≫ π = π)
    (hdiv : ∀ σ : G, ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 := by
  obtain ⟨τ, rfl⟩ := hdiv σ
  obtain ⟨g, hg⟩ := hπ (ρ τ - 1) (by
    erw [Preadditive.sub_comp, hρ, Category.id_comp, sub_self])
  have hR : ((ℓ : End Y)) ^ m = 0 := by
    rw [← Nat.cast_pow, ← nsmul_one]
    exact hℓ
  have hτ : ρ τ = 1 + ℓ * g := by
    rw [← nsmul_eq_mul, ← hg]
    exact (add_sub_cancel _ _).symm
  rw [map_pow, hτ, one_add_natCast_mul_pow_eq_one hR]

namespace Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Actions trivial modulo `ℓ` by `ℓ`-divisible groups are trivial**, for the reduction
`π : Y ⟶ Z` modulo `ℓ` given by a distinguished triangle `Y --ℓ--> Y --π--> Z ⟶ Y⟦1⟧`. -/
theorem MonoidHom.eq_one_of_distinguished {Y Z : C} {ℓ m : ℕ} (π : Y ⟶ Z) (δ : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 Y) π δ ∈ distTriang C) (hℓ : (ℓ ^ m) • 𝟙 Y = 0)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, ρ τ ≫ π = π)
    (hdiv : ∀ σ : G, ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 := by
  refine CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow π hℓ (fun f hf ↦ ?_)
    ρ hρ hdiv σ
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT f hf
  let g' : Y ⟶ Y := g
  have hg' : f = g' ≫ (ℓ • 𝟙 Y) := hg
  rw [Preadditive.comp_nsmul, Category.comp_id] at hg'
  exact ⟨g', hg'⟩

end Pretriangulated

end CategoryTheory
