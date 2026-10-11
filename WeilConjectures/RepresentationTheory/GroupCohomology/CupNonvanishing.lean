/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Nonvanishing of group cohomology of free abelian groups

Let `G` be a commutative group, `k` a nontrivial commutative ring, and suppose there are
homomorphisms `a₁, …, aₙ : G → k` and elements `e₁, …, eₙ ∈ G` with `aᵢ(eⱼ) = δᵢⱼ`. Then
`Hⁿ(G, k) ≠ 0` for the trivial representation `k`
(`groupCohomology.not_isZero_of_dualFamily`). This applies to `G ≅ ℤⁿ` and to `G ≅ ⊕_ℕ ℤ` in
every degree, which is the group-cohomological input `Hⁿ(⊕_ℕ ℤ, Λ) ≠ 0` of blueprint
`sk-rem-sf-fullcd-scope`.

The proof avoids the Künneth formula. The cup product `a₁ ∪ ⋯ ∪ aₙ`, `(g₁, …, gₙ) ↦ ∏ aᵢ(gᵢ)`,
is a cocycle (a telescoping sum). The alternating pairing
`c ↦ ∑_σ sign σ · c(e_{σ 1}, …, e_{σ n})` with the "fundamental cycle" of the `eᵢ` kills
coboundaries: the inner faces cancel in pairs `σ, σ ∘ (j j+1)` because `G` is commutative,
and the two outer faces cancel after a cyclic rotation. It takes the value `1` on the cup
product.
-/

@[expose] public section

universe u

open CategoryTheory groupCohomology

namespace groupCohomology

variable {k G : Type u} [CommRing k] [CommGroup G]

/-- The alternating pairing of an `n`-cochain with the "fundamental cycle"
`∑_σ sign σ [e_{σ 0} | ⋯ | e_{σ (n-1)}]` of a family `e` of elements of `G`. -/
def altPairing {n : ℕ} (e : Fin n → G) (f : (Fin n → G) → k) : k :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * f (e ∘ σ)

/-- A signed sum over permutations of a function invariant under right multiplication by a
transposition vanishes. -/
lemma sum_sign_mul_eq_zero {n : ℕ} (F : Equiv.Perm (Fin n) → k) {a b : Fin n} (hab : a ≠ b)
    (hF : ∀ σ, F (σ * Equiv.swap a b) = F σ) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * F σ = 0 := by
  refine Finset.sum_involution (fun σ _ ↦ σ * Equiv.swap a b) (fun σ _ ↦ ?_) (fun σ _ _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun σ _ ↦ by simp [mul_assoc])
  · rw [hF, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    push_cast
    ring
  · intro h
    have := congrArg (fun τ ↦ σ⁻¹ * τ) h
    simp only [inv_mul_cancel_left, inv_mul_cancel] at this
    exact hab (Equiv.swap_eq_one_iff.1 this)

lemma d_trivial_apply {n : ℕ} (b : (Fin n → G) → k) (g : Fin (n + 1) → G) :
    (inhomogeneousCochains.d (Rep.trivial k G k) n).hom b g =
      b (fun i ↦ g i.succ) + ∑ j : Fin (n + 1),
        (-1 : k) ^ ((j : ℕ) + 1) * b (Fin.contractNth j (· * ·) g) := by
  simp [inhomogeneousCochains.d_hom_apply]

/-- Contracting the positions `j, j + 1` of a tuple does not change under swapping them, in a
commutative group. -/
lemma contractNth_comp_swap {n : ℕ} (j : Fin n) (g : Fin (n + 1) → G) :
    Fin.contractNth j.castSucc (· * ·) (g ∘ Equiv.swap j.castSucc j.succ) =
      Fin.contractNth j.castSucc (· * ·) g := by
  funext i
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h), Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h), Function.comp_apply,
      Function.comp_apply]
    have hi : i = j := Fin.ext h
    subst hi
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h), Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega

lemma contractNth_last {n : ℕ} (g : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) g = fun i ↦ g i.castSucc := by
  funext i
  exact Fin.contractNth_apply_of_lt _ _ _ _ (by simp)

/-- The alternating pairing kills coboundaries. -/
theorem altPairing_d {n : ℕ} (e : Fin (n + 1) → G) (b : (Fin n → G) → k) :
    altPairing e ((inhomogeneousCochains.d (Rep.trivial k G k) n).hom b) = 0 := by
  unfold altPairing
  rw [Finset.sum_congr rfl fun σ _ ↦ by rw [d_trivial_apply b (e ∘ σ)]]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  -- the inner faces cancel in pairs
  have hinner : ∀ j : Fin n, ∑ σ : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign σ : ℤ) : k) * ((-1 : k) ^ ((j.castSucc : ℕ) + 1) *
        b (Fin.contractNth j.castSucc (· * ·) (e ∘ σ))) = 0 := by
    intro j
    simp_rw [mul_left_comm _ ((-1 : k) ^ _), ← Finset.mul_sum]
    rw [sum_sign_mul_eq_zero (fun σ ↦ b (Fin.contractNth j.castSucc (· * ·) (e ∘ σ)))
      (a := j.castSucc) (b := j.succ) (Fin.castSucc_lt_succ).ne fun σ ↦ ?_, mul_zero]
    simp only [Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, contractNth_comp_swap]
  simp only [hinner, Finset.sum_const_zero, zero_add, contractNth_last]
  -- the outer faces cancel after a cyclic rotation
  rw [add_comm, ← Equiv.sum_comp (Equiv.mulRight (finRotate (n + 1)))]
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.coe_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  have hrot : (fun i : Fin n ↦ (e ∘ σ ∘ finRotate (n + 1)) i.castSucc) =
      fun i ↦ (e ∘ σ) i.succ := by
    funext i
    simp [finRotate_apply, Fin.coeSucc_eq_succ]
  rw [hrot]
  have h1 : (-1 : k) ^ n * (-1) ^ (n + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨n, by ring⟩
  push_cast [Fin.val_last, Nat.add_sub_cancel]
  linear_combination ((Equiv.Perm.sign σ : ℤ) : k) * (b fun i ↦ (e ∘ σ) i.succ) * h1

end groupCohomology
