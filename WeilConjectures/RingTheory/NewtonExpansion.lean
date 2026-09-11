/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
public import WeilConjectures.Mathlib.RingTheory.Binomial

/-!
# The Newton expansion of a function on `ℤ`

A function `Q : ℤ → G` killed by the `(n + 1)`-st iterate of the forward difference operator
`Δ_[1]` is determined by the finitely many values `Δ_[1]^[i] Q 0`, `i ≤ n`: it is the
corresponding truncated Newton series in the integer binomial coefficients `Ring.choose m i`.

Mathlib's `shift_eq_sum_fwdDiff_iter` is the Gregory–Newton formula on `ℕ`; the statement here is
its rigid form on all of `ℤ`, which is the one-variable case of `lem:deg-difference-criterion` of
the blueprint chapter on the degree of an isogeny.

## Main results

* `Ring.fwdDiff_choose`: `Δ_[1] (fun r ↦ Ring.choose r (i + 1)) = fun r ↦ Ring.choose r i`.
* `eq_sum_choose_smul_fwdDiff_iter`: the Newton expansion itself.

The rigidity statement it rests on, `eq_zero_of_fwdDiff_iter_eq_zero`, is in
`WeilConjectures/Mathlib/Algebra/Group/ForwardDiff.lean`.
-/

@[expose] public section

open Finset fwdDiff

variable {G : Type*} [AddCommGroup G]

/-- The forward difference operator shifts the binomial coefficients of a binomial ring: this is
Pascal's rule `Ring.choose_succ_succ`. -/
theorem Ring.fwdDiff_choose {R : Type*} [CommRing R] [BinomialRing R] (i : ℕ) :
    Δ_[(1 : R)] (fun r : R ↦ Ring.choose r (i + 1)) = fun r ↦ Ring.choose r i := by
  funext r
  simp [_root_.fwdDiff, Ring.choose_succ_succ]

/-- The truncated Newton series with coefficients `c`. -/
private def newtonSum (c : ℕ → G) (n : ℕ) : ℤ → G :=
  fun m ↦ ∑ i ∈ range n, Ring.choose m i • c i

private lemma fwdDiff_newtonSum (c : ℕ → G) (n : ℕ) :
    Δ_[(1 : ℤ)] (newtonSum c (n + 1)) = newtonSum (fun i ↦ c (i + 1)) n := by
  have hfun : newtonSum c (n + 1) = ∑ i ∈ range (n + 1), fun m : ℤ ↦ Ring.choose m i • c i := by
    funext m
    simp [newtonSum]
  rw [hfun, fwdDiff_finsetSum]
  funext m
  simp only [Finset.sum_apply, fwdDiff_smul_const, Pi.smul_apply']
  rw [Finset.sum_range_succ']
  simp only [Ring.fwdDiff_choose, newtonSum]
  simp [_root_.fwdDiff]

private lemma newtonSum_zero (c : ℕ → G) (n : ℕ) : newtonSum c (n + 1) 0 = c 0 := by
  rw [newtonSum, Finset.sum_range_succ']
  simp

private lemma fwdDiff_iter_newtonSum (c : ℕ → G) (n : ℕ) :
    Δ_[(1 : ℤ)]^[n] (newtonSum c n) = 0 := by
  induction n generalizing c with
  | zero => funext m; simp [newtonSum]
  | succ n ih => rw [Function.iterate_succ_apply, fwdDiff_newtonSum, ih]

private lemma fwdDiff_iter_newtonSum_apply_zero (c : ℕ → G) {j n : ℕ} (hj : j < n) :
    Δ_[(1 : ℤ)]^[j] (newtonSum c n) 0 = c j := by
  induction j generalizing c n with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hj
    simpa using newtonSum_zero c n
  | succ j ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply, fwdDiff_newtonSum, ih _ (by omega)]

/-- **The Newton expansion of a function on `ℤ`.** If `Δ_[1]^[n + 1] Q = 0`, then `Q` is the
truncated Newton series built from its iterated differences at `0` and the integer binomial
coefficients. -/
theorem eq_sum_choose_smul_fwdDiff_iter {n : ℕ} {Q : ℤ → G} (h : Δ_[(1 : ℤ)]^[n + 1] Q = 0)
    (m : ℤ) : Q m = ∑ i ∈ range (n + 1), Ring.choose m i • Δ_[(1 : ℤ)]^[i] Q 0 := by
  set c : ℕ → G := fun i ↦ Δ_[(1 : ℤ)]^[i] Q 0 with hc
  have hzero : Q - newtonSum c (n + 1) = 0 := by
    refine eq_zero_of_fwdDiff_iter_eq_zero (n := n) ?_ fun j hj ↦ ?_
    · rw [fwdDiff_iter_sub, h, fwdDiff_iter_newtonSum, sub_zero]
    · rw [fwdDiff_iter_sub, Pi.sub_apply, fwdDiff_iter_newtonSum_apply_zero c hj, hc, sub_self]
  have := congrFun (sub_eq_zero.mp hzero) m
  simpa [newtonSum] using this
