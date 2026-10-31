/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Tactic.Ring
/-!
Orthogonality of characters with values in a local ring, using the normalized
averaging idempotent instead of cancellation in a domain.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open scoped BigOperators
universe u v
namespace AddChar

/-- A nontrivial character sums to zero over a local ring when the group order is a unit.
Source: the averaging-projector argument in the latest blueprint's character-integral proof.

Put `S = ∑ g, ψ g`. Translation gives `ψ(b) S = S`, hence `S² = |G| S`.
Thus `e = |G|⁻¹ S` is idempotent. In a local ring either `e` or `1-e` is a unit.
The first possibility forces `e = 1` and then every `ψ(b) = 1`, a contradiction.
The second forces `e = 0`, hence `S = 0`.
(blueprint: lem-fd-local-character-orthogonality) -/
theorem sum_eq_zero_of_ne_one_of_isLocalRing
    {G : Type u} [AddGroup G] [Fintype G] {A : Type v} [CommRing A]
    [IsLocalRing A] [Invertible (Fintype.card G : A)] (ψ : AddChar G A) (hψ : ψ ≠ 1) :
    ∑ g, ψ g = 0 := by
  classical
  let S : A := ∑ g, ψ g
  have htrans (b : G) : ψ b * S = S := by
    dsimp [S]
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft b) _ _ fun a ↦ by
      rw [Equiv.coe_addLeft, AddChar.map_add_eq_mul]
  let e : A := ⅟(Fintype.card G : A) * S
  have he : e * e = e := by
    have hSS : S * S = (Fintype.card G : A) * S := by
      change (∑ g, ψ g) * S = _
      rw [Finset.sum_mul]
      simp only [htrans, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [e]
    calc
      _ = ⅟(Fintype.card G : A) * ⅟(Fintype.card G : A) * (S * S) := by ring
      _ = _ := by rw [hSS]; simp [mul_assoc]
  have hemul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · have he1 : e = 1 := by
      have := hu.mul_left_cancel (by simpa using hemul : e * (1 - e) = e * 0)
      exact (sub_eq_zero.mp this).symm
    apply False.elim
    apply hψ
    ext b
    have hb : ψ b * e = e := by
      dsimp [e]
      rw [mul_left_comm, htrans]
    simpa [he1] using hb
  · have he0 : e = 0 := by
      exact hu.mul_right_cancel (by simpa using hemul : e * (1 - e) = 0 * (1 - e))
    have := congrArg ((Fintype.card G : A) * ·) he0
    simpa [e, mul_assoc] using this

end AddChar
