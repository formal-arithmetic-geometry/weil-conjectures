/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import WeilConjectures.RingTheory.FiniteGabberPolynomialRelation

/-!
# Gabber's polynomial for a finite algebra over a Zariski pair

Let `(A, I)` be a Zariski pair and `B` a finite `A`-algebra with `B / IB ≅ B₁ × B₂`. Any lift
`b ∈ B` of `(1, 0)` is annihilated by a monic polynomial `X^d (X - 1) + ∑ aⱼ X^j` with `d ≥ 1`
and `aⱼ ∈ I`.

## Implementation details

After a faithfully flat base change `A → A''` (étale followed by a localization), the lifted
idempotent splits the algebra, the first factor becomes a quotient of `A''` and the image of `b`
in the second factor lies in the extended ideal. Multiplying a monic annihilator of the second
component (reducing to a power of `X`) by `X - 1 - a'` gives the relation upstairs, which
descends to `A` by universal injectivity of faithfully flat maps.

## References

* [Stacks, Tag 0EM0]
* [Stacks, Tag 07M4]
* [Stacks, Tag 00DV]
* [Stacks, Tag 00H5]
* [Stacks, Tag 05CK]
-/

@[expose] public section

universe u v w z

open Polynomial
open scoped BigOperators

namespace Algebra

/-- A lift of `(1,0)` in a finite algebra over a Zariski pair is annihilated by a monic
polynomial of the form `X^d (X-1) + ∑ aⱼ X^j`, with `d ≥ 1` and `aⱼ ∈ I`.
The compatibility condition on `e` says that the quotient decomposition is one of
`A/I`-algebras, rather than merely of rings. -/
theorem exists_monic_aeval_eq_zero_gabber_polynomial
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (d : ℕ) (a : Fin (d + 1) → A) (f : A[X]),
      1 ≤ d ∧ (∀ j, a j ∈ I) ∧ f.Monic ∧ aeval b f = 0 ∧
        f = X ^ d * (X - 1) + ∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ) := by
  classical
  obtain ⟨S, f, hS, d, hd, hzero⟩ :=
    exists_gabber_relation_after_base_change I hI B₁ B₂ e he h₁ b hb
  let : Algebra A S := f.toAlgebra
  let : Module.FaithfullyFlat A S := hS
  let L : (Fin (d + 1) → I) →ₗ[A] B :=
    ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ))
  have hq : (LinearMap.range L).mkQ ((b - 1) * b ^ d) = 0 :=
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := S)
      (B ⧸ LinearMap.range L)) (hzero.trans (map_zero _).symm)
  have hmem : (b - 1) * b ^ d ∈ LinearMap.range L := by
    simpa only [← (LinearMap.range L).ker_mkQ, LinearMap.mem_ker] using hq
  obtain ⟨c, hc⟩ := hmem
  let a : Fin (d + 1) → A := fun j ↦ -(c j : A)
  have ha : ∀ j, a j ∈ I := fun j ↦ I.neg_mem (c j).property
  have hrel : (b - 1) * b ^ d +
      ∑ j : Fin (d + 1), algebraMap A B (a j) * b ^ (j : ℕ) = 0 := by
    have hc' : ∑ j : Fin (d + 1), algebraMap A B (c j : A) * b ^ (j : ℕ) =
        (b - 1) * b ^ d := by
      simpa [L, LinearMap.sum_apply, Algebra.smul_def] using hc
    simp only [a, map_neg, neg_mul, Finset.sum_neg_distrib, hc', add_neg_cancel]
  refine ⟨d, a, X ^ d * (X - 1) + ∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ),
    hd, ha, ?_, ?_, rfl⟩
  · nontriviality A
    rw [mul_sub, mul_one, ← pow_succ, sub_eq_add_neg, add_assoc]
    apply monic_X_pow_add
    have hsum : (∑ j : Fin (d + 1), C (a j) * X ^ (j : ℕ)).degree ≤ (d : WithBot ℕ) := by
      apply (degree_sum_le _ _).trans
      apply Finset.sup_le
      intro j hj
      exact (degree_C_mul_X_pow_le _ _).trans
        (WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ j.isLt))
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · rw [degree_neg, degree_X_pow]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d)
    · exact lt_of_le_of_lt hsum (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  · rw [aeval_add, aeval_mul, aeval_X_pow, aeval_sub, aeval_X]
    simp only [map_one, map_pow, map_sum, map_mul, aeval_def]
    simp only [eval₂_C, eval₂_X]
    calc
      b ^ d * (b - 1) + ∑ x, (algebraMap A B) (a x) * b ^ (x : ℕ) =
          (b - 1) * b ^ d + ∑ x, (algebraMap A B) (a x) * b ^ (x : ℕ) := by ring
      _ = 0 := hrel

end Algebra
