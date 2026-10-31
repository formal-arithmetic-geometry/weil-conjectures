/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

/-! # Integrating polynomial coordinate differences on the integer lattice

Source: Stacks Project, Varieties, Tag 0BEM, final arithmetic argument.
-/

@[expose] public section

namespace MvPolynomial

private theorem power_antidifference (m : ℕ) :
    ∃ A : Polynomial ℚ, A.natDegree ≤ m + 1 ∧ A.eval 0 = 0 ∧
      ∀ x : ℚ, A.eval (x + 1) - A.eval x = x ^ m := by
  let f : ℕ → ℚ := fun n ↦ ∑ i ∈ Finset.range n, (i : ℚ) ^ m
  obtain ⟨B, hB, he⟩ := Polynomial.exists_degree_lt_eval_eq_of_sub
    (Q := Polynomial.X ^ m) (d := m + 1) (by
      simpa using (show (m : WithBot ℕ) < (m + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self m))
    (f := f) (by
      intro n
      simp [f, Finset.sum_range_succ])
  have hdeg : B.natDegree ≤ m + 1 := by
    by_cases hz : B = 0
    · simp [hz]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hB
      exact Nat.le_of_lt_succ this
  have hpoly : B.comp (Polynomial.X + 1) - B = Polynomial.X ^ m := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_sub, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
    rw [← Nat.cast_add_one, he, he]
    simp [f, Finset.sum_range_succ]
  refine ⟨B, hdeg, ?_, fun x ↦ ?_⟩
  · simpa [f] using he 0
  · have h := congrArg (Polynomial.eval x) hpoly
    simpa using h

private theorem totalDegree_polynomial_eval₂ {r : ℕ} (A : Polynomial ℚ)
    (j : Fin r) :
    (A.eval₂ C (X j) : MvPolynomial (Fin r) ℚ).totalDegree ≤ A.natDegree := by
  rw [Polynomial.eval₂_eq_sum]
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by
    simpa using Polynomial.le_natDegree_of_mem_supp i hi)

private theorem eval_polynomial_eval₂ {r : ℕ} (A : Polynomial ℚ)
    (j : Fin r) (x : Fin r → ℚ) :
    eval x (A.eval₂ C (X j)) = A.eval (x j) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [Polynomial.eval₂_add, hA, hB]
  | monomial i c => simp [Polynomial.eval₂_monomial]

private theorem exists_antidifference {r d : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℚ)
    (hQ : Q = 0 ∨ Q.totalDegree < d) :
    ∃ A : MvPolynomial (Fin (r + 1)) ℚ, A.totalDegree ≤ d ∧
      (∀ x : Fin r → ℚ, eval (Fin.cons 0 x) A = 0) ∧
      ∀ (x : Fin r → ℚ) (t : ℚ),
        eval (Fin.cons (t + 1) x) A - eval (Fin.cons t x) A =
          eval (Fin.cons t x) Q := by
  classical
  rcases hQ with rfl | hQ
  · exact ⟨0, by simp, by simp, by simp⟩
  choose B hB hB0 hBe using power_antidifference
  let q := finSuccEquiv ℚ r Q
  let A := ∑ i ∈ q.support,
    rename Fin.succ (q.coeff i) * (B i).eval₂ C (X 0)
  refine ⟨A, ?_, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro i hi
    have hq : q.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hiQ := totalDegree_coeff_finSuccEquiv_add_le Q i hq
    calc
      _ ≤ (rename Fin.succ (q.coeff i)).totalDegree +
          ((B i).eval₂ C (X 0) : MvPolynomial (Fin (r + 1)) ℚ).totalDegree :=
        totalDegree_mul _ _
      _ ≤ (q.coeff i).totalDegree + (i + 1) :=
        Nat.add_le_add (totalDegree_rename_le _ _) ((totalDegree_polynomial_eval₂ _ _).trans
          (hB i))
      _ ≤ d := by dsimp [q] at *; omega
  · intro x
    simp only [A, map_sum, map_mul, eval_rename, eval_polynomial_eval₂, Fin.cons_zero,
      hB0, mul_zero, Finset.sum_const_zero]
  · intro x t
    simp only [A, map_sum, map_mul, eval_rename, eval_polynomial_eval₂, Fin.cons_zero,
      Function.comp_def, Fin.cons_succ, ← Finset.sum_sub_distrib, ← mul_sub, hBe]
    rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_eq_sum,
      Polynomial.sum_def]

private theorem integer_constant_of_succ (g : ℤ → ℚ)
    (hg : ∀ t, g (t + 1) = g t) (t : ℤ) : g t = g 0 := by
  induction t using Int.induction_on with
  | zero => rfl
  | succ t ih => exact (hg t).trans ih
  | pred t ih =>
    have h := hg (-(t : ℤ) - 1)
    rw [sub_add_cancel] at h
    exact h.symm.trans ih

/-- A function on an integer lattice whose coordinate differences have total degree less
than d is a polynomial of total degree at most d.
Source: Stacks Project, Varieties, Tag 0BEM, last paragraph
(blueprint: lem-sc-coordinate-differences-polynomial).

Proof: Induct on the number of coordinates. Integrate the first difference term by term
in that coordinate, choosing zero value on its zero slice. A monomial of degree e has an
antidifference of degree at most e+1, by the univariate Newton-series theorem. Subtract
this polynomial from the function; the remainder is constant along the first coordinate,
including negative integers by backward induction. On the zero slice the other differences
are the restrictions of the given differences, with the same degree bounds. Induction on
the number of coordinates gives the polynomial on that slice. Add its renamed polynomial
to the antidifference. The zero-variable case is the constant function. -/
theorem exists_eval_eq_of_coordinate_differences (r d : ℕ) (f : (Fin r → ℤ) → ℚ)
    (hf : ∀ j : Fin r, ∃ Q : MvPolynomial (Fin r) ℚ,
      (Q = 0 ∨ Q.totalDegree < d) ∧ ∀ n : Fin r → ℤ,
        f (Function.update n j (n j + 1)) - f n = eval (fun i ↦ (n i : ℚ)) Q) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d ∧
      ∀ n : Fin r → ℤ, eval (fun i ↦ (n i : ℚ)) P = f n := by
  classical
  induction r with
  | zero =>
    refine ⟨C (f 0), by simp, fun n ↦ ?_⟩
    simp only [eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ r ih =>
    obtain ⟨Q, hQ, heQ⟩ := hf 0
    obtain ⟨A, hA, hA0, heA⟩ := exists_antidifference Q hQ
    have hconst (n : Fin r → ℤ) (t : ℤ) :
        f (Fin.cons t n) - eval (Fin.cons (t : ℚ) (fun i ↦ (n i : ℚ))) A =
          f (Fin.cons 0 n) := by
      have hstep (t : ℤ) :
          f (Fin.cons (t + 1) n) - eval (Fin.cons ((t + 1 : ℤ) : ℚ)
            (fun i ↦ (n i : ℚ))) A =
          f (Fin.cons t n) - eval (Fin.cons (t : ℚ) (fun i ↦ (n i : ℚ))) A := by
        have hq := heQ (Fin.cons t n)
        have ha := heA (fun i ↦ (n i : ℚ)) (t : ℚ)
        have hu : Function.update (Fin.cons t n : Fin (r + 1) → ℤ) 0 (t + 1) =
            (Fin.cons (t + 1) n : Fin (r + 1) → ℤ) := by
          ext i
          refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
        simp only [Fin.cons_zero] at hq
        rw [hu] at hq
        have hc (t : ℤ) : (fun i ↦ (((Fin.cons t n : Fin (r + 1) → ℤ) i) : ℚ)) =
            Fin.cons (t : ℚ) (fun i ↦ (n i : ℚ)) := by
          ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
        rw [hc] at hq
        push_cast
        linarith
      have h := integer_constant_of_succ
        (fun t ↦ f (Fin.cons t n) -
          eval (Fin.cons (t : ℚ) (fun i ↦ (n i : ℚ))) A) hstep t
      simpa only [Int.cast_zero, hA0, sub_zero] using h
    have hslice : ∀ j : Fin r, ∃ Q : MvPolynomial (Fin r) ℚ,
        (Q = 0 ∨ Q.totalDegree < d) ∧ ∀ n : Fin r → ℤ,
          f (Fin.cons 0 (Function.update n j (n j + 1))) - f (Fin.cons 0 n) =
            eval (fun i ↦ (n i : ℚ)) Q := by
      intro j
      obtain ⟨B, hB, heB⟩ := hf j.succ
      let b := eval₂Hom C (Fin.cases 0 X) B
      refine ⟨b, ?_, ?_⟩
      · rcases hB with rfl | hB
        · left; simp [b]
        · right
          have hdeg : b.totalDegree ≤ B.totalDegree := by
            change (eval₂Hom C (Fin.cases 0 X) B).totalDegree ≤ B.totalDegree
            conv_lhs => rw [B.as_sum]
            simp only [map_sum]
            apply totalDegree_finsetSum_le
            intro m hm
            rw [eval₂Hom_monomial]
            apply (totalDegree_mul _ _).trans
            simp only [totalDegree_C, zero_add, Finsupp.prod]
            apply (totalDegree_finsetProd _ _).trans
            apply le_trans (Finset.sum_le_sum fun i hi ↦ ?_) (le_totalDegree hm)
            exact (totalDegree_pow _ _).trans (by
              have : ((Fin.cases (0 : MvPolynomial (Fin r) ℚ)
                  (fun j ↦ (X j : MvPolynomial (Fin r) ℚ)) :
                    Fin (r + 1) → MvPolynomial (Fin r) ℚ) i).totalDegree ≤ 1 := by
                refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
              simpa using Nat.mul_le_mul_left (m i) this)
          exact hdeg.trans_lt hB
      · intro n
        have hu : Function.update (Fin.cons 0 n : Fin (r + 1) → ℤ) j.succ (n j + 1) =
            (Fin.cons 0 (Function.update n j (n j + 1)) : Fin (r + 1) → ℤ) := by
          ext i
          refine Fin.cases ?_ (fun i ↦ ?_) i
          · simp [Ne.symm (Fin.succ_ne_zero j)]
          · simp [Function.update_apply]
        have he := heB (Fin.cons 0 n)
        simp only [Fin.cons_succ, hu] at he
        rw [he]
        change _ = eval (fun i ↦ (n i : ℚ)) (eval₂ C (Fin.cases 0 X) B)
        rw [eval_eval₂]
        have hC : (eval (fun i ↦ (n i : ℚ))).comp C = RingHom.id ℚ := by
          ext a; simp
        rw [hC, eval₂_id]
        apply congrArg (fun g : Fin (r + 1) → ℚ ↦ eval g B)
        funext i
        refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
    obtain ⟨B, hB, heB⟩ := ih (fun n ↦ f (Fin.cons 0 n)) hslice
    refine ⟨A + rename Fin.succ B, (totalDegree_add _ _).trans
      (max_le hA ((totalDegree_rename_le _ _).trans hB)), fun n ↦ ?_⟩
    rw [map_add, eval_rename]
    have hn : n = Fin.cons (n 0) (fun i ↦ n i.succ) := (Fin.cons_self_tail n).symm
    have hc : (fun i ↦ (n i : ℚ)) =
        Fin.cons (n 0 : ℚ) (fun i ↦ (n i.succ : ℚ)) := by
      ext i; refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl
    have h := hconst (fun i ↦ n i.succ) (n 0)
    rw [← hn] at h
    rw [hc]
    have hb := heB (fun i ↦ n i.succ)
    change eval (fun i ↦ (n i.succ : ℚ)) B = _ at hb
    rw [show Fin.cons (n 0 : ℚ) (fun i ↦ (n i.succ : ℚ)) ∘ Fin.succ =
      (fun i ↦ (n i.succ : ℚ)) from rfl, hb]
    linarith

end MvPolynomial
