/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The cyclotomic character of a power of Frobenius

Let `K` be an algebraically closed field of characteristic `p`, let `q = p ^ a`, and let `ℓ ≠ p`
be a prime. The `ℓ`-adic cyclotomic character records the scalar in `ℤ_ℓˣ` by which a ring
automorphism of `K` acts on the cyclotomic Tate module `ℤ_ℓ(1)`, because the automorphism acts on
each group of `ℓ^n`-th roots of unity by raising to that power.

The `q`-power (arithmetic) Frobenius `σ : x ↦ x ^ q` raises every root of unity to the `q`-th
power, so it acts on `ℤ_ℓ(1)` as multiplication by `q`. Consequently the geometric Frobenius
`F = σ⁻¹` acts as multiplication by `q⁻¹`, which is a genuine unit of `ℤ_ℓ` precisely because
`ℓ ∤ q`; this is a formal consequence of the first statement, since the cyclotomic character is a
homomorphism into `ℤ_ℓˣ`. The same formulas describe the action on the localisation
`ℚ_ℓ(1) = ℤ_ℓ(1)[1/ℓ]`, since that action is obtained from the one on `ℤ_ℓ(1)` by extension of
scalars.

## Main declarations

* `cyclotomicCharacter_frobeniusEquiv_pow`: the `q = p ^ a` power Frobenius acts on `ℤ_ℓ(1)` by
  the scalar `q`.
* `cyclotomicCharacter_frobeniusEquiv_pow_inv_mul`: the geometric Frobenius acts by the inverse
  scalar `q⁻¹`, a unit of `ℤ_ℓ`.

## Blueprint

`cyclotomicCharacter_frobeniusEquiv_pow` and `cyclotomicCharacter_frobeniusEquiv_pow_inv_mul`
implement `sk-p-cyclotomic`.
-/

@[expose] public section

variable (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : ℕ)
  (l : ℕ) [Fact l.Prime]

/-- The `q = p ^ a` power arithmetic Frobenius acts on the cyclotomic Tate module `ℤ_ℓ(1)` as
multiplication by `q`.
(blueprint: `sk-p-cyclotomic`) -/
theorem cyclotomicCharacter_frobeniusEquiv_pow (hl : l ≠ p) :
    ((cyclotomicCharacter K l ((frobeniusEquiv K p) ^ a) : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) ^ a := by
  sorry

/-- The geometric Frobenius `F = σ⁻¹`, the inverse of the `q = p ^ a` power Frobenius, acts on the
cyclotomic Tate module `ℤ_ℓ(1)` as multiplication by `q⁻¹`; in particular `q` is a unit of `ℤ_ℓ`,
which holds because `ℓ ≠ p`.
(blueprint: `sk-p-cyclotomic`) -/
theorem cyclotomicCharacter_frobeniusEquiv_pow_inv_mul (hl : l ≠ p) :
    ((cyclotomicCharacter K l (((frobeniusEquiv K p) ^ a)⁻¹) : ℤ_[l]ˣ) : ℤ_[l]) *
      (p : ℤ_[l]) ^ a = 1 := by
  rw [← cyclotomicCharacter_frobeniusEquiv_pow K p a l hl, map_inv]
  exact_mod_cast (cyclotomicCharacter K l ((frobeniusEquiv K p) ^ a)).inv_mul
