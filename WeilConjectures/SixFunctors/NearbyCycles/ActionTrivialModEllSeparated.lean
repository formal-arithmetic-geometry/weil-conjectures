/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ActionTrivialModEll

/-!

# Actions trivial modulo `ℓ` on `ℓ`-adically separated objects

The integral form of `CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow`: on an
object `Y` whose endomorphisms are `ℓ`-adically separated (no nonzero endomorphism is divisible
by every power of `ℓ`, e.g. nearby cycles with `𝒪_E`-coefficients, whose endomorphisms form a
finitely generated `𝒪_E`-module), a group in which every element is an `ℓ ^ m`-th power for every
`m` (e.g. a pro-`p` group, `p ≠ ℓ`) acting trivially modulo `ℓ` acts trivially
(`CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow_of_separated`). Indeed
`(1 + ℓ g) ^ (ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`
(`exists_one_add_natCast_mul_pow_sub_one_eq`).

-/

@[expose] public section

open CategoryTheory

/-- In any ring, `(1 + ℓ x) ^ (ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`. -/
theorem exists_one_add_natCast_mul_pow_sub_one_eq {R : Type*} [Ring R] (ℓ m : ℕ) (x : R) :
    ∃ y : R, (1 + ℓ * x) ^ (ℓ ^ m) - 1 = (ℓ : R) ^ (m + 1) * y := by
  obtain ⟨q, hq⟩ := dvd_sub_pow_of_dvd_sub (R := Polynomial ℤ) (p := ℓ)
    (a := 1 + (ℓ : Polynomial ℤ) * Polynomial.X) (b := 1) ⟨Polynomial.X, by ring⟩ m
  have := congrArg (Polynomial.aeval x) hq
  simp only [one_pow, map_sub, map_pow, map_add, map_one, map_mul, map_natCast,
    Polynomial.aeval_X] at this
  exact ⟨_, this⟩

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Actions trivial modulo `ℓ` on `ℓ`-adically separated objects are trivial**: let `Y` be an
object no nonzero endomorphism of which is divisible by every power of `ℓ`, and `π : Y ⟶ Z` such
that every endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by `ℓ`. A group in which every
element is an `ℓ ^ m`-th power for every `m`, acting on `Y` by `ρ` with `ρ τ ≫ π = π` for all
`τ`, acts trivially. -/
theorem MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow_of_separated {Y Z : C} (π : Y ⟶ Z)
    {ℓ : ℕ} (hsep : ∀ f : End Y, (∀ m : ℕ, ∃ g : End Y, f = (ℓ ^ m) • g) → f = 0)
    (hπ : ∀ f : End Y, f ≫ π = 0 → ∃ g : End Y, f = ℓ • g)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, ρ τ ≫ π = π)
    (hdiv : ∀ (m : ℕ) (σ : G), ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 := by
  rw [← sub_eq_zero]
  refine hsep _ fun m ↦ ?_
  obtain ⟨τ, rfl⟩ := hdiv m σ
  obtain ⟨g, hg⟩ := hπ (ρ τ - 1) (by
    erw [Preadditive.sub_comp, hρ, Category.id_comp, sub_self])
  have hτ : ρ τ = 1 + ℓ * g := by
    rw [← nsmul_eq_mul, ← hg]
    exact (add_sub_cancel _ _).symm
  obtain ⟨y, hy⟩ := exists_one_add_natCast_mul_pow_sub_one_eq ℓ m g
  refine ⟨ℓ * y, ?_⟩
  rw [map_pow, hτ, hy, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_assoc]

end CategoryTheory
