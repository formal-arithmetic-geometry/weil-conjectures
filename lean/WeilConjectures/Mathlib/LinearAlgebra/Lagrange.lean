/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!
# Lagrange idempotents over a finite field

Let `k` be a finite field with `q` elements and `A` a `k`-algebra. For `u ∈ A` with `u ^ q = u`,
evaluating the Lagrange basis of `k` (all of `k` as nodes) at `u` gives a complete family of
orthogonal idempotents `(e_c)_{c ∈ k}` with `e_c (u - c) = 0`: it splits `A` according to the
value of `u`. Products over a finite index type give the analogue for `u : n → A`, indexed by
`kⁿ`.

## Main definitions

- `FiniteField.lagrangeAt`: the evaluation at `u` of the Lagrange basis polynomial at `c`.
- `FiniteField.lagrangeIdem`: the product `∏ᵢ lagrangeAt (u i) (a i)` for `a : n → k`.

## Main statements

- `FiniteField.sum_lagrangeIdem`, `FiniteField.lagrangeIdem_mul_lagrangeIdem` and
  `FiniteField.lagrangeIdem_mul_sub`: the `lagrangeIdem` sum to `1`, are pairwise orthogonal
  and are supported on the loci `u = a`.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace Polynomial

/-- If `r * (u - c) = 0`, then `r * f(u) = f(c) * r` for every polynomial `f`. -/
theorem mul_eval₂_eq_of_mul_sub_eq_zero {k A : Type*} [CommRing k] [CommRing A] (ψ : k →+* A)
    {u r : A} {c : k} (h : r * (u - ψ c) = 0) (f : k[X]) :
    r * f.eval₂ ψ u = ψ (f.eval c) * r := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := c)
  have := congrArg (eval₂ ψ u) hg
  simp only [eval₂_sub, eval₂_C, eval₂_mul, eval₂_X] at this
  linear_combination r * this + g.eval₂ ψ u * h

end Polynomial

namespace FiniteField

variable {k A : Type*} [Field k] [Fintype k] [CommRing A] [DecidableEq k]

/-- The evaluation at `u` of the Lagrange basis polynomial of the finite field `k` at the node
`c`. When `u ^ q = u`, these form a complete family of orthogonal idempotents. -/
def lagrangeAt (ψ : k →+* A) (u : A) (c : k) : A :=
  (Lagrange.basis Finset.univ id c).eval₂ ψ u

/-- The `FiniteField.lagrangeAt ψ u c` sum to `1`. -/
lemma sum_lagrangeAt (ψ : k →+* A) (u : A) : ∑ c, lagrangeAt ψ u c = 1 := by
  simp only [lagrangeAt, ← eval₂_finsetSum]
  rw [Lagrange.sum_basis (Set.injOn_id _) Finset.univ_nonempty, eval₂_one]

/-- If `u ^ q = u`, then `FiniteField.lagrangeAt ψ u c` is supported on the locus `u = c`. -/
lemma lagrangeAt_mul_sub (ψ : k →+* A) {u : A} (hu : u ^ Fintype.card k = u) (c : k) :
    lagrangeAt ψ u c * (u - ψ c) = 0 := by
  have h := prod_sub_eq_zero_of_pow_card_eq ψ hu
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c)] at h
  simp only [lagrangeAt, Lagrange.basis, Lagrange.basisDivisor, eval₂_finsetProd, eval₂_mul,
    eval₂_C, eval₂_sub, eval₂_X, Finset.prod_mul_distrib, id]
  linear_combination (∏ j ∈ Finset.univ.erase c, ψ (c - j)⁻¹) * h

/-- If `u ^ q = u`, the `FiniteField.lagrangeAt ψ u c` are pairwise orthogonal. -/
lemma lagrangeAt_mul_lagrangeAt (ψ : k →+* A) {u : A} (hu : u ^ Fintype.card k = u)
    {c c' : k} (h : c ≠ c') : lagrangeAt ψ u c * lagrangeAt ψ u c' = 0 := by
  have := Polynomial.mul_eval₂_eq_of_mul_sub_eq_zero ψ (lagrangeAt_mul_sub ψ hu c)
    (Lagrange.basis Finset.univ id c')
  have h0 : (Lagrange.basis Finset.univ id c').eval c = 0 :=
    Lagrange.eval_basis_of_ne (v := id) h.symm (Finset.mem_univ c)
  rwa [h0, map_zero, zero_mul] at this

/-- At `u = c`, the Lagrange idempotent at the node `c` is `1`. -/
lemma lagrangeAt_self (ψ : k →+* A) (c : k) : lagrangeAt ψ (ψ c) c = 1 := by
  have h1 : (Lagrange.basis Finset.univ id c).eval c = 1 :=
    Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (Finset.mem_univ c)
  rw [lagrangeAt, eval₂_at_apply, h1, map_one]

/-- `FiniteField.lagrangeAt` commutes with ring homomorphisms. -/
lemma map_lagrangeAt {B : Type*} [CommRing B] (g : A →+* B) (ψ : k →+* A) (u : A) (c : k) :
    g (lagrangeAt ψ u c) = lagrangeAt (g.comp ψ) (g u) c :=
  hom_eval₂ _ _ _ _

section Pi

variable {n : Type*} [Fintype n]

/-- For a family `u` of elements of a `k`-algebra indexed by `n` and `a : n → k`, the product of
the `FiniteField.lagrangeAt ψ (u i) (a i)`. When `u i ^ q = u i` for all `i`, these form a
complete family of orthogonal idempotents indexed by `kⁿ`, cutting out the loci `u = a`. -/
def lagrangeIdem (ψ : k →+* A) (u : n → A) (a : n → k) : A :=
  ∏ i, lagrangeAt ψ (u i) (a i)

/-- The `FiniteField.lagrangeIdem ψ u a` sum to `1`. -/
lemma sum_lagrangeIdem [DecidableEq n] (ψ : k →+* A) (u : n → A) :
    ∑ a, lagrangeIdem ψ u a = 1 := by
  simp only [lagrangeIdem]
  rw [← Fintype.prod_sum]
  simp [sum_lagrangeAt]

/-- If `u i ^ q = u i` for all `i`, then `FiniteField.lagrangeIdem ψ u a` is supported on the
locus `u = a`. -/
lemma lagrangeIdem_mul_sub (ψ : k →+* A) {u : n → A}
    (hu : ∀ i, u i ^ Fintype.card k = u i) (a : n → k) (i : n) :
    lagrangeIdem ψ u a * (u i - ψ (a i)) = 0 := by
  classical
  rw [lagrangeIdem, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm,
    lagrangeAt_mul_sub ψ (hu i), zero_mul]

/-- If `u i ^ q = u i` for all `i`, the `FiniteField.lagrangeIdem ψ u a` are pairwise
orthogonal. -/
lemma lagrangeIdem_mul_lagrangeIdem (ψ : k →+* A) {u : n → A}
    (hu : ∀ i, u i ^ Fintype.card k = u i) {a b : n → k} (h : a ≠ b) :
    lagrangeIdem ψ u a * lagrangeIdem ψ u b = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  rw [lagrangeIdem, lagrangeIdem, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (lagrangeAt_mul_lagrangeAt ψ (hu i) hi)

/-- At `u = a`, the Lagrange idempotent indexed by `a` is `1`. -/
lemma lagrangeIdem_self (ψ : k →+* A) (a : n → k) :
    lagrangeIdem ψ (fun i ↦ ψ (a i)) a = 1 := by
  simp [lagrangeIdem, lagrangeAt_self]

/-- `FiniteField.lagrangeIdem` commutes with ring homomorphisms. -/
lemma map_lagrangeIdem {B : Type*} [CommRing B] (g : A →+* B) (ψ : k →+* A) (u : n → A)
    (a : n → k) : g (lagrangeIdem ψ u a) = lagrangeIdem (g.comp ψ) (fun i ↦ g (u i)) a := by
  simp [lagrangeIdem, map_lagrangeAt]

end Pi

end FiniteField

end
