/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The geometric Frobenius of an algebraic extension of a finite field

For a finite field `k` and an algebraic extension `K` of `k`, the arithmetic Frobenius
`x ↦ x ^ #k` is an automorphism of `K` over `k`
(`FiniteField.frobeniusAlgEquivOfAlgebraic`). Its inverse is the *geometric Frobenius*
`FiniteField.geometricFrobenius`, the generator of the Galois group used in the Weil
conjectures: on the `ℓ`-adic cohomology of a variety over `k` it is the operator whose
traces count points.

## Main definitions

- `FiniteField.geometricFrobenius`: the geometric Frobenius of an algebraic extension of
  a finite field, the inverse of the arithmetic Frobenius, characterized by
  `FiniteField.geometricFrobenius_pow_card` and `FiniteField.geometricFrobenius_eq_iff`.
-/

@[expose] public section

namespace FiniteField

variable (k : Type*) [Field k] [Finite k]
variable (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- The geometric Frobenius of an algebraic extension `K` of a finite field `k`, the
inverse of the arithmetic Frobenius `x ↦ x ^ #k`
(`FiniteField.frobeniusAlgEquivOfAlgebraic`). It is characterized by
`FiniteField.geometricFrobenius_pow_card`: it is the unique `#k`-th root. -/
noncomputable def geometricFrobenius : K ≃ₐ[k] K :=
  letI : Fintype k := Fintype.ofFinite k
  (frobeniusAlgEquivOfAlgebraic k K).symm

@[simp]
theorem geometricFrobenius_pow_card (x : K) : geometricFrobenius k K x ^ Nat.card k = x := by
  let : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact (frobeniusAlgEquivOfAlgebraic k K).apply_symm_apply x

/-- The geometric Frobenius of an algebraic extension of a finite field `k` is
characterized as the inverse of raising to the `#k`-th power. -/
theorem geometricFrobenius_eq_iff {x y : K} :
    geometricFrobenius k K x = y ↔ y ^ Nat.card k = x := by
  refine ⟨fun h ↦ h ▸ geometricFrobenius_pow_card k K x, fun h ↦ h ▸ ?_⟩
  let : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact (frobeniusAlgEquivOfAlgebraic k K).symm_apply_apply y

end FiniteField
