/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.Ring

/-!
# Shifting the variables of a multivariate polynomial

We record the compatibility of `MvPolynomial.eval` with `MvPolynomial.bind₁` and the fact that
substituting `X i + C (c i)` for `X i` changes a polynomial only in degrees below its total
degree: this is the polynomial input to `lem:deg-difference-lowers-degree` of the blueprint
chapter on the degree of an isogeny.
-/

@[expose] public section

namespace MvPolynomial

theorem eval_bind₁ {σ τ R : Type*} [CommSemiring R] (g : τ → R) (f : σ → MvPolynomial τ R)
    (φ : MvPolynomial σ R) : eval g (bind₁ f φ) = eval (fun i ↦ eval g (f i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

variable {σ R : Type*} [CommRing R]

/-- Auxiliary predicate: every monomial occurring in `p` has total degree `< n`. -/
private def DegLT (n : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ u : σ →₀ ℕ, n ≤ u.degree → coeff u p = 0

private lemma degree_eq_sum (u : σ →₀ ℕ) : u.degree = u.sum fun _ e ↦ e := rfl

private lemma degLT_of_totalDegree_lt {n m : ℕ} {p : MvPolynomial σ R} (h₁ : p.totalDegree ≤ m)
    (h₂ : m < n) : DegLT n p :=
  fun _ hu ↦ coeff_eq_zero_of_totalDegree_lt (by rw [← Finsupp.degree_apply]; omega)

private lemma DegLT.mono {n m : ℕ} {p : MvPolynomial σ R} (h : DegLT n p) (hnm : n ≤ m) :
    DegLT m p :=
  fun u hu ↦ h u (le_trans hnm hu)

private lemma DegLT.totalDegree_le {n : ℕ} {p : MvPolynomial σ R} (h : DegLT (n + 1) p) :
    p.totalDegree ≤ n := by
  rw [totalDegree]
  refine Finset.sup_le fun u hu ↦ ?_
  by_contra hlt
  exact (mem_support_iff.mp hu) (h u (by rw [degree_eq_sum]; omega))

private lemma DegLT.sub {n : ℕ} {p q : MvPolynomial σ R} (hp : DegLT n p) (hq : DegLT n q) :
    DegLT n (p - q) :=
  fun u hu ↦ by rw [coeff_sub, hp u hu, hq u hu, sub_zero]

private lemma DegLT.add {n : ℕ} {p q : MvPolynomial σ R} (hp : DegLT n p) (hq : DegLT n q) :
    DegLT n (p + q) :=
  fun u hu ↦ by rw [coeff_add, hp u hu, hq u hu, add_zero]

private lemma DegLT.sum {ι : Type*} {n : ℕ} {s : Finset ι} {f : ι → MvPolynomial σ R}
    (h : ∀ i ∈ s, DegLT n (f i)) : DegLT n (∑ i ∈ s, f i) :=
  fun u hu ↦ by rw [coeff_sum]; exact Finset.sum_eq_zero fun i hi ↦ h i hi u hu

private lemma DegLT.mul_right {a b : ℕ} {p q : MvPolynomial σ R} (hp : DegLT a p)
    (hq : q.totalDegree ≤ b) : DegLT (a + b) (p * q) := by
  classical
  intro u hu
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  have hsum : x.1.degree + x.2.degree = u.degree := by rw [← hx, map_add]
  by_cases h2 : x.2.degree ≤ b
  · rw [hp x.1 (by omega), zero_mul]
  · have hz : coeff x.2 q = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by rw [← Finsupp.degree_apply]; omega)
    rw [hz, mul_zero]

private lemma DegLT.mul_left {a b : ℕ} {p q : MvPolynomial σ R} (hp : p.totalDegree ≤ a)
    (hq : DegLT b q) : DegLT (a + b) (p * q) := by
  classical
  intro u hu
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  have hsum : x.1.degree + x.2.degree = u.degree := by rw [← hx, map_add]
  by_cases h1 : x.1.degree ≤ a
  · rw [hq x.2 (by omega), mul_zero]
  · have hz : coeff x.1 p = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by rw [← Finsupp.degree_apply]; omega)
    rw [hz, zero_mul]

private lemma totalDegree_X_le (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  have h : (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 := by
    rw [← C_mul_X_eq_monomial, C_1, one_mul]
  rw [h]
  simpa using totalDegree_monomial_le (Finsupp.single i 1) (1 : R)

private lemma totalDegree_X_add_C_le (i : σ) (c : R) :
    (X i + C c : MvPolynomial σ R).totalDegree ≤ 1 :=
  le_trans (totalDegree_add _ _) (by simp [totalDegree_X_le i])

private lemma totalDegree_X_add_C_pow_le (i : σ) (c : R) (k : ℕ) :
    ((X i + C c : MvPolynomial σ R) ^ k).totalDegree ≤ k :=
  le_trans (totalDegree_pow _ _) (by simpa using Nat.mul_le_mul_left k (totalDegree_X_add_C_le i c))

private lemma degLT_X_add_C_pow_sub (i : σ) (c : R) (k : ℕ) :
    DegLT k ((X i + C c : MvPolynomial σ R) ^ k - X i ^ k) := by
  induction k with
  | zero => simp [DegLT]
  | succ k ih =>
    have key : (X i + C c : MvPolynomial σ R) ^ (k + 1) - X i ^ (k + 1) =
        C c * (X i + C c) ^ k + X i * ((X i + C c) ^ k - X i ^ k) := by ring
    rw [key]
    refine DegLT.add ?_ ?_
    · exact (DegLT.mul_right (degLT_of_totalDegree_lt (le_of_eq (totalDegree_C c)) Nat.one_pos)
        (totalDegree_X_add_C_pow_le i c k)).mono (by omega)
    · exact (DegLT.mul_left (totalDegree_X_le i) ih).mono (by omega)

private lemma degLT_prod_X_add_C_sub (c : σ → R) (s : Finset σ) (k : σ → ℕ) :
    DegLT (∑ i ∈ s, k i)
      ((∏ i ∈ s, (X i + C (c i) : MvPolynomial σ R) ^ k i) -
        ∏ i ∈ s, (X i : MvPolynomial σ R) ^ k i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [DegLT]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have key : ∀ A B C' D : MvPolynomial σ R, A * C' - B * D = (A - B) * C' + B * (C' - D) := by
      intro A B C' D; ring
    rw [key]
    refine DegLT.add (DegLT.mul_right (degLT_X_add_C_pow_sub j (c j) (k j)) ?_)
      (DegLT.mul_left ?_ ih)
    · refine le_trans (totalDegree_finsetProd _ _) (Finset.sum_le_sum fun i _ ↦ ?_)
      exact totalDegree_X_add_C_pow_le i (c i) (k i)
    · exact le_trans (totalDegree_pow _ _)
        (by simpa using Nat.mul_le_mul_left (k j) (totalDegree_X_le j))

/-- Shifting the variables of a multivariate polynomial by constants lowers the total degree of the
difference: if `p` has total degree at most `n + 1`, then `p (X + c) - p (X)` has total degree at
most `n`. -/
theorem totalDegree_bind₁_X_add_C_sub_le (c : σ → R) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p.totalDegree ≤ n + 1) :
    (bind₁ (fun i ↦ X i + C (c i)) p - p).totalDegree ≤ n := by
  classical
  refine DegLT.totalDegree_le (n := n) ?_
  have hsum : bind₁ (fun i ↦ X i + C (c i)) p - p = ∑ w ∈ p.support,
      (bind₁ (fun i ↦ X i + C (c i)) (monomial w (coeff w p)) - monomial w (coeff w p)) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← p.as_sum]
  rw [hsum]
  refine DegLT.sum fun w hw ↦ ?_
  have hdeg : ∑ i ∈ w.support, w i ≤ n + 1 := le_trans (le_totalDegree hw) hp
  have key : bind₁ (fun i ↦ X i + C (c i)) (monomial w (coeff w p)) - monomial w (coeff w p) =
      C (coeff w p) * ((∏ i ∈ w.support, (X i + C (c i) : MvPolynomial σ R) ^ w i) -
        ∏ i ∈ w.support, (X i : MvPolynomial σ R) ^ w i) := by
    rw [bind₁_monomial, monomial_eq, Finsupp.prod, mul_sub]
  rw [key]
  exact ((degLT_prod_X_add_C_sub c w.support w).mono hdeg).mul_left
    (le_of_eq (totalDegree_C _)) |>.mono (by omega)

end MvPolynomial
