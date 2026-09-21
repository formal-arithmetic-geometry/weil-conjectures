/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
public import WeilConjectures.Mathlib.Algebra.MvPolynomial.Funext
public import WeilConjectures.Mathlib.Algebra.MvPolynomial.Monad
public import WeilConjectures.RingTheory.NewtonExpansion

/-!
# Numerical polynomials in several variables

A function `P : ℤ ^ r → ℤ` is a *numerical polynomial of total degree at most `d`* if it is the
restriction to the integer points of a polynomial in `ℚ[T_1, …, T_r]` of total degree at most `d`.
This file introduces the predicate `IsNumericalPolynomial` and develops the difference calculus
for it.

## Main results

* `IsNumericalPolynomial`: the predicate itself (`def:deg-numerical`).
* `IsNumericalPolynomial.existsUnique`: the representing polynomial is unique, so that the total
  degree of a numerical polynomial is well defined (`lem:deg-numerical-unique`).
* `IsNumericalPolynomial.fwdDiff`: a difference operator `Δ_[v]` lowers the degree by one
  (`lem:deg-difference-lowers-degree`), with the consequences
  `IsNumericalPolynomial.fwdDiffComp_eq_zero` and
  `IsNumericalPolynomial.exists_fwdDiffComp_eq_const`.
* `isNumericalPolynomial_of_fwdDiffComp_eq_zero`: the converse, `lem:deg-difference-criterion`: a
  function killed by every composite of `d + 1` standard-basis difference operators is a numerical
  polynomial of total degree at most `d`. The resulting characterisation is
  `isNumericalPolynomial_iff_fwdDiffComp_eq_zero`.
* `IsNumericalPolynomial.fwdDiffComp_cons_add_arg` and
  `IsNumericalPolynomial.fwdDiffComp_zsmul_arg`: on a numerical polynomial of total degree at most
  `d`, the composite of `d` difference operators is additive and homogeneous in each of its `d`
  directions; homogeneity in all `d` directions at once multiplies the composite by the product of
  the scalars.
* `IsNumericalPolynomial.comp_addHom`: substituting an additive map, equivalently a tuple
  of integer linear forms, into a numerical polynomial of total degree at most `d` gives a
  numerical polynomial of total degree at most `d` (`lem:deg-numerical-substitution`), with the
  special case `IsNumericalPolynomial.comp_append_neg` used in the reduction to very ample line
  bundles in the proof of `thm:deg-snapper`.

The alternating sum expansion of a composite of difference operators
(`lem:deg-difference-explicit`) is `fwdDiffComp_eq_sum_powerset` in
`WeilConjectures/Mathlib/Algebra/Group/ForwardDiff.lean`.

## References

The blueprint chapter on the degree of an isogeny, section `sec:deg-numerical`.
-/

@[expose] public section

open Finset Nat fwdDiff MvPolynomial

variable {r : ℕ}

/-- A function `P : ℤ ^ r → ℤ` is a *numerical polynomial of total degree at most `d`* if it is the
restriction to the integer points of a polynomial with rational coefficients of total degree at
most `d`. This is `def:deg-numerical` of the blueprint. -/
def IsNumericalPolynomial (d : ℕ) (P : (Fin r → ℤ) → ℤ) : Prop :=
  ∃ p : MvPolynomial (Fin r) ℚ, p.totalDegree ≤ d ∧
    ∀ m : Fin r → ℤ, (P m : ℚ) = eval (fun i ↦ (m i : ℚ)) p

namespace IsNumericalPolynomial

variable {d e : ℕ} {P : (Fin r → ℤ) → ℤ}

lemma mono (h : IsNumericalPolynomial d P) (hde : d ≤ e) : IsNumericalPolynomial e P := by
  obtain ⟨p, hp, hP⟩ := h
  exact ⟨p, hp.trans hde, hP⟩

/-- **The representing polynomial of a numerical polynomial is unique.**
This is `lem:deg-numerical-unique` of the blueprint. -/
theorem existsUnique (h : IsNumericalPolynomial d P) :
    ∃! p : MvPolynomial (Fin r) ℚ, p.totalDegree ≤ d ∧
      ∀ m : Fin r → ℤ, (P m : ℚ) = eval (fun i ↦ (m i : ℚ)) p := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨p, ⟨hp, hP⟩, fun q hq ↦ MvPolynomial.funext_intCast fun m ↦ ?_⟩
  rw [← hq.2 m, hP m]

/-- A numerical polynomial of total degree at most `0` is constant. -/
theorem exists_eq_const (h : IsNumericalPolynomial 0 P) : ∃ c : ℤ, P = Function.const _ c := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨P 0, funext fun m ↦ ?_⟩
  have hC : p = C (coeff 0 p) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)
  have hcast : (P m : ℚ) = (P 0 : ℚ) := by rw [hP m, hP 0, hC]; simp
  exact_mod_cast hcast

end IsNumericalPolynomial

/-- A constant function is a numerical polynomial of total degree at most `0`. -/
lemma isNumericalPolynomial_const (c : ℤ) :
    IsNumericalPolynomial (r := r) 0 (Function.const _ c) :=
  ⟨C (c : ℚ), (totalDegree_C _).le, fun _ ↦ by simp⟩

/-- Being a numerical polynomial of total degree at most `0` means being constant. -/
lemma isNumericalPolynomial_zero_iff {P : (Fin r → ℤ) → ℤ} :
    IsNumericalPolynomial 0 P ↔ ∃ c : ℤ, P = Function.const _ c :=
  ⟨IsNumericalPolynomial.exists_eq_const,
    fun ⟨c, hc⟩ ↦ hc ▸ isNumericalPolynomial_const c⟩

namespace IsNumericalPolynomial

variable {d e : ℕ} {P : (Fin r → ℤ) → ℤ}

/-- **Difference operators lower the degree.** This is `lem:deg-difference-lowers-degree` of the
blueprint. -/
theorem fwdDiff (h : IsNumericalPolynomial (d + 1) P) (v : Fin r → ℤ) :
    IsNumericalPolynomial d (Δ_[v] P) := by
  obtain ⟨p, hp, hP⟩ := h
  refine ⟨bind₁ (fun i ↦ X i + C ((v i : ℚ))) p - p,
    totalDegree_bind₁_X_add_C_sub_le _ _ _ hp, fun m ↦ ?_⟩
  have hΔ : (Δ_[v] P) m = P (m + v) - P m := rfl
  have harg : (fun i ↦ (((m + v) i : ℤ) : ℚ)) =
      fun i ↦ eval (fun i ↦ ((m i : ℤ) : ℚ)) (X i + C ((v i : ℚ))) := by
    funext i
    simp
  rw [hΔ, Int.cast_sub, hP (m + v), hP m, map_sub, eval_bind₁, ← harg]

/-- A difference operator kills a numerical polynomial of total degree at most `0`. -/
theorem fwdDiff_eq_zero (h : IsNumericalPolynomial 0 P) (v : Fin r → ℤ) : Δ_[v] P = 0 := by
  obtain ⟨c, rfl⟩ := h.exists_eq_const
  funext m
  simp [_root_.fwdDiff]

/-- Applying `e` difference operators to a numerical polynomial of total degree at most `d + e`
gives a numerical polynomial of total degree at most `d`. -/
theorem fwdDiffComp (h : IsNumericalPolynomial (d + e) P) (v : Fin e → (Fin r → ℤ)) :
    IsNumericalPolynomial d (_root_.fwdDiffComp v P) := by
  induction e generalizing P with
  | zero => simpa using h
  | succ e ih =>
    rw [fwdDiffComp_succ']
    refine ih ?_ _
    rw [show d + (e + 1) = (d + e) + 1 from by omega] at h
    exact h.fwdDiff (v 0)

/-- A composite of `d + 1` difference operators kills a numerical polynomial of total degree at
most `d`. -/
theorem fwdDiffComp_eq_zero (h : IsNumericalPolynomial d P) (v : Fin (d + 1) → (Fin r → ℤ)) :
    _root_.fwdDiffComp v P = 0 := by
  have h' : IsNumericalPolynomial (0 + d) P := by rwa [Nat.zero_add]
  rw [fwdDiffComp_succ]
  exact (h'.fwdDiffComp _).fwdDiff_eq_zero (v 0)

/-- A composite of `d` difference operators turns a numerical polynomial of total degree at most
`d` into a constant function. -/
theorem exists_fwdDiffComp_eq_const (h : IsNumericalPolynomial d P) (v : Fin d → (Fin r → ℤ)) :
    ∃ c : ℤ, _root_.fwdDiffComp v P = Function.const _ c := by
  have h' : IsNumericalPolynomial (0 + d) P := by rwa [Nat.zero_add]
  exact (h'.fwdDiffComp v).exists_eq_const

/-- **The top difference is additive in each of its directions.** For a numerical polynomial of
total degree at most `d + 1`, the composite of `d + 1` difference operators whose leading
direction is a sum `a + b` is the sum of the composites for `a` and for `b`: the remainder
`Δ_[a] Δ_[b] ⋯` left by the operator identity `Δ_[a + b] = Δ_[a] + Δ_[b] + Δ_[a] Δ_[b]` is a
composite of `d + 2` difference operators, hence vanishes. -/
theorem fwdDiffComp_cons_add_arg (h : IsNumericalPolynomial (d + 1) P) (a b : Fin r → ℤ)
    (v : Fin d → (Fin r → ℤ)) :
    _root_.fwdDiffComp (Fin.cons (a + b) v) P =
      _root_.fwdDiffComp (Fin.cons a v) P + _root_.fwdDiffComp (Fin.cons b v) P := by
  rw [_root_.fwdDiffComp_cons_add_arg, h.fwdDiffComp_eq_zero (Fin.cons a (Fin.cons b v)), add_zero]

/-- **The top difference is homogeneous in its leading direction**: scaling it by an integer `n`
multiplies the composite by `n`. This is additivity in that direction, read as additivity of the
map `n ↦ Δ_[n • a] Δ_[v 0] ⋯ Δ_[v (d - 1)] P` on `ℤ`, so it covers negative `n` as well. -/
theorem fwdDiffComp_cons_zsmul_arg (h : IsNumericalPolynomial (d + 1) P) (n : ℤ) (a : Fin r → ℤ)
    (v : Fin d → (Fin r → ℤ)) :
    _root_.fwdDiffComp (Fin.cons (n • a) v) P = n • _root_.fwdDiffComp (Fin.cons a v) P := by
  have hadd : ∀ x y : ℤ, _root_.fwdDiffComp (Fin.cons ((x + y) • a) v) P =
      _root_.fwdDiffComp (Fin.cons (x • a) v) P + _root_.fwdDiffComp (Fin.cons (y • a) v) P :=
    fun x y ↦ by rw [add_smul, h.fwdDiffComp_cons_add_arg]
  simpa using (AddMonoidHom.mk' (fun x : ℤ ↦ _root_.fwdDiffComp (Fin.cons (x • a) v) P)
    hadd).map_zsmul n 1

/-- **The top difference is homogeneous in every direction at once**: scaling the `d` directions
of a composite of `d` difference operators by integers `n₀, …, n_{d-1}` multiplies the composite
by `n₀ ⋯ n_{d-1}`, on a numerical polynomial of total degree at most `d`.

This is what makes the intersection number homogeneous in every slot at once. -/
theorem fwdDiffComp_zsmul_arg : ∀ {d : ℕ} {P : (Fin r → ℤ) → ℤ}, IsNumericalPolynomial d P →
    ∀ (n : Fin d → ℤ) (v : Fin d → (Fin r → ℤ)),
      _root_.fwdDiffComp (fun j ↦ n j • v j) P = (∏ j, n j) • _root_.fwdDiffComp v P
  | 0, _, _, _, _ => by simp
  | d + 1, P, h, n, v => by
    -- peel off the leading direction `n 0 • v 0` and apply the induction hypothesis to the rest
    have hcons : (fun j ↦ n j • v j) = Fin.cons (n 0 • v 0) fun i ↦ n i.succ • v i.succ := by
      funext j
      induction j using Fin.cases with
      | zero => simp
      | succ i => simp
    -- the leading direction contributes the factor `n 0`, by homogeneity in one direction
    have hlead : _root_.fwdDiffComp (fun i ↦ v i.succ) (Δ_[n 0 • v 0] P) =
        n 0 • _root_.fwdDiffComp v P := by
      have h1 := h.fwdDiffComp_cons_zsmul_arg (n 0) (v 0) fun i ↦ v i.succ
      rw [fwdDiffComp_succ' (Fin.cons (n 0 • v 0) _), fwdDiffComp_succ' (Fin.cons (v 0) _)] at h1
      simp only [Fin.cons_zero, Fin.cons_succ] at h1
      rw [h1, ← fwdDiffComp_succ']
    rw [hcons, fwdDiffComp_succ' (Fin.cons (n 0 • v 0) _)]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [fwdDiffComp_zsmul_arg (h.fwdDiff (n 0 • v 0)), hlead, smul_smul, Fin.prod_univ_succ,
      mul_comm]

end IsNumericalPolynomial

section Criterion

variable {d : ℕ}

/-- The composite `Δ_{j₁} ⋯ Δ_{j_k}` of the standard-basis difference operators indexed by a list
of coordinates. -/
private def fwdDiffSingle (l : List (Fin r)) (P : (Fin r → ℤ) → ℤ) : (Fin r → ℤ) → ℤ :=
  fwdDiffList (l.map fun a ↦ Pi.single a 1) P

private lemma fwdDiffSingle_cons (a : Fin r) (l : List (Fin r)) (P : (Fin r → ℤ) → ℤ) :
    fwdDiffSingle (a :: l) P = Δ_[Pi.single a 1] (fwdDiffSingle l P) := by
  simp [fwdDiffSingle, fwdDiffList_cons]

private lemma fwdDiffSingle_append (l₁ l₂ : List (Fin r)) (P : (Fin r → ℤ) → ℤ) :
    fwdDiffSingle (l₁ ++ l₂) P = fwdDiffSingle l₁ (fwdDiffSingle l₂ P) := by
  simp [fwdDiffSingle, List.map_append, fwdDiffList_append]

private lemma fwdDiffSingle_replicate (n : ℕ) (a : Fin r) (P : (Fin r → ℤ) → ℤ) :
    fwdDiffSingle (List.replicate n a) P = Δ_[Pi.single a 1]^[n] P := by
  simp [fwdDiffSingle, List.map_replicate, fwdDiffList_replicate]

private lemma fwdDiffComp_eq_fwdDiffSingle (j : Fin d → Fin r) (P : (Fin r → ℤ) → ℤ) :
    fwdDiffComp (fun k ↦ Pi.single (j k) 1) P = fwdDiffSingle (List.ofFn j) P := by
  rw [fwdDiffComp_eq_fwdDiffList, fwdDiffSingle, List.map_ofFn, Function.comp_def]

/-- The hypothesis of `lem:deg-difference-criterion`, restated for lists of coordinates. -/
private lemma forall_fwdDiffSingle_eq_zero {P : (Fin r → ℤ) → ℤ}
    (h : ∀ j : Fin (d + 1) → Fin r, fwdDiffComp (fun k ↦ Pi.single (j k) 1) P = 0)
    (l : List (Fin r)) (hl : l.length = d + 1) : fwdDiffSingle l P = 0 := by
  have hj := h fun k : Fin (d + 1) ↦ l[(k : ℕ)]'(by omega)
  rw [fwdDiffComp_eq_fwdDiffSingle] at hj
  rwa [show List.ofFn (fun k : Fin (d + 1) ↦ l[(k : ℕ)]'(by omega)) = l from
    List.ext_getElem (by simp [hl]) fun n h₁ h₂ ↦ by rw [List.getElem_ofFn]] at hj

private lemma cons_add_single_zero (m₀ : ℤ) (m' : Fin r → ℤ) :
    (Fin.cons m₀ m' : Fin (r + 1) → ℤ) + Pi.single (0 : Fin (r + 1)) 1 =
      Fin.cons (m₀ + 1) m' := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [Fin.succ_ne_zero i]

private lemma cons_zero_add_single_succ (m' : Fin r → ℤ) (a : Fin r) :
    (Fin.cons 0 m' : Fin (r + 1) → ℤ) + Pi.single a.succ 1 = Fin.cons 0 (m' + Pi.single a 1) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    simp [Pi.single_apply, (Fin.succ_ne_zero a).symm, Fin.succ_inj]

/-- Freezing all but the first variable turns `Δ_[Pi.single 0 1]` into the one-variable difference
operator `Δ_[1]`. -/
private lemma fwdDiff_iter_comp_cons (F : (Fin (r + 1) → ℤ) → ℤ) (m' : Fin r → ℤ) (i : ℕ) :
    Δ_[(1 : ℤ)]^[i] (fun m₀ ↦ F (Fin.cons m₀ m')) =
      fun m₀ ↦ (Δ_[Pi.single (0 : Fin (r + 1)) 1]^[i] F) (Fin.cons m₀ m') := by
  induction i generalizing F with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext m₀
    simp only [_root_.fwdDiff, cons_add_single_zero]

/-- Difference operators in the last `r` coordinates commute with restricting the first coordinate
to `0`. -/
private lemma fwdDiffSingle_comp_cons_zero (F : (Fin (r + 1) → ℤ) → ℤ) (l : List (Fin r)) :
    fwdDiffSingle l (fun m' ↦ F (Fin.cons 0 m')) =
      fun m' ↦ fwdDiffSingle (l.map Fin.succ) F (Fin.cons 0 m') := by
  induction l generalizing F with
  | nil => simp [fwdDiffSingle]
  | cons a l ih =>
    rw [fwdDiffSingle_cons, ih, List.map_cons, fwdDiffSingle_cons]
    funext m'
    simp only [_root_.fwdDiff, cons_zero_add_single_succ]

/-- The multivariate polynomial in the variable `X i₀` representing the binomial coefficient
`m ↦ Ring.choose m n`. -/
private noncomputable def binomialPoly (σ : Type*) (i₀ : σ) (n : ℕ) : MvPolynomial σ ℚ :=
  C ((n ! : ℚ)⁻¹) * ∏ k ∈ range n, (X i₀ - C (k : ℚ))

private lemma totalDegree_binomialPoly_le {σ : Type*} (i₀ : σ) (n : ℕ) :
    (binomialPoly σ i₀ n).totalDegree ≤ n := by
  have hle : ∀ k ∈ range n, (X i₀ - C (k : ℚ)).totalDegree ≤ 1 := fun k _ ↦
    le_trans (totalDegree_sub _ _) (by rw [totalDegree_X, totalDegree_C]; simp)
  have hprod : (∏ k ∈ range n, (X i₀ - C (k : ℚ))).totalDegree ≤ n :=
    le_trans (totalDegree_finsetProd _ _) (le_trans (Finset.sum_le_sum hle) (by simp))
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact hprod

private lemma eval_binomialPoly {σ : Type*} (i₀ : σ) (n : ℕ) (f : σ → ℚ) :
    eval f (binomialPoly σ i₀ n) = Ring.choose (f i₀) n := by
  rw [Ring.choose_eq_inv_factorial_mul_prod_range, binomialPoly]
  simp

/-- **The converse of the degree-lowering lemma.** If every composite of `d + 1` standard-basis
difference operators kills `P`, then `P` is a numerical polynomial of total degree at most `d`.
This is `lem:deg-difference-criterion` of the blueprint. -/
theorem isNumericalPolynomial_of_fwdDiffComp_eq_zero {P : (Fin r → ℤ) → ℤ}
    (h : ∀ j : Fin (d + 1) → Fin r, fwdDiffComp (fun k ↦ Pi.single (j k) 1) P = 0) :
    IsNumericalPolynomial d P := by
  induction r generalizing d with
  | zero =>
    have hP : P = Function.const _ (P 0) := by
      funext m
      rw [Subsingleton.elim m 0]
      rfl
    exact (isNumericalPolynomial_zero_iff.mpr ⟨P 0, hP⟩).mono (Nat.zero_le d)
  | succ r ih =>
    have hlist : ∀ l : List (Fin (r + 1)), l.length = d + 1 → fwdDiffSingle l P = 0 :=
      forall_fwdDiffSingle_eq_zero h
    set c : ℕ → (Fin r → ℤ) → ℤ :=
      fun i m' ↦ (Δ_[Pi.single (0 : Fin (r + 1)) 1]^[i] P) (Fin.cons 0 m') with hc
    -- the one-variable Newton expansion in the first coordinate
    have hexp : ∀ (m₀ : ℤ) (m' : Fin r → ℤ),
        P (Fin.cons m₀ m') = ∑ i ∈ range (d + 1), Ring.choose m₀ i * c i m' := by
      intro m₀ m'
      have hP : Δ_[Pi.single (0 : Fin (r + 1)) 1]^[d + 1] P = 0 := by
        rw [← fwdDiffSingle_replicate]
        exact hlist _ (by simp)
      have hQ : Δ_[(1 : ℤ)]^[d + 1] (fun m₀ ↦ P (Fin.cons m₀ m')) = 0 := by
        rw [fwdDiff_iter_comp_cons, hP]
        rfl
      rw [eq_sum_choose_smul_fwdDiff_iter hQ m₀]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_eq_mul, hc, fwdDiff_iter_comp_cons]
    -- the coefficient functions satisfy the hypothesis with `d` replaced by `d - i`
    have hcnum : ∀ i : Fin (d + 1), IsNumericalPolynomial (d - i) (c (i : ℕ)) := by
      intro i
      refine ih fun j ↦ ?_
      rw [fwdDiffComp_eq_fwdDiffSingle, hc]
      have hzero : fwdDiffSingle ((List.ofFn j).map Fin.succ)
          (Δ_[Pi.single (0 : Fin (r + 1)) 1]^[(i : ℕ)] P) = 0 := by
        rw [← fwdDiffSingle_replicate (i : ℕ) (0 : Fin (r + 1)), ← fwdDiffSingle_append]
        refine hlist _ ?_
        have : (i : ℕ) ≤ d := by omega
        simp only [List.length_append, List.length_map, List.length_ofFn, List.length_replicate]
        omega
      rw [fwdDiffSingle_comp_cons_zero, hzero]
      rfl
    choose p hpdeg hpeval using hcnum
    refine ⟨∑ i : Fin (d + 1), rename Fin.succ (p i) * binomialPoly (Fin (r + 1)) 0 (i : ℕ),
      ?_, ?_⟩
    · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ ↦ ?_)
      refine le_trans (totalDegree_mul _ _) ?_
      have h₁ : (rename Fin.succ (p i)).totalDegree ≤ d - (i : ℕ) :=
        le_trans (totalDegree_rename_le _ _) (hpdeg i)
      have h₂ := totalDegree_binomialPoly_le (0 : Fin (r + 1)) (i : ℕ)
      have h₃ : (i : ℕ) ≤ d := by omega
      omega
    · intro m
      obtain ⟨m₀, m', rfl⟩ : ∃ (m₀ : ℤ) (m' : Fin r → ℤ), m = Fin.cons m₀ m' :=
        ⟨m 0, Fin.tail m, (Fin.cons_self_tail m).symm⟩
      rw [map_sum, hexp m₀ m', ← Fin.sum_univ_eq_sum_range (fun i ↦ Ring.choose m₀ i * c i m')]
      push_cast
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcomp : ((fun k : Fin (r + 1) ↦ (((Fin.cons m₀ m' : Fin (r + 1) → ℤ) k : ℤ) : ℚ)) ∘
          Fin.succ) = fun k ↦ ((m' k : ℤ) : ℚ) := by
        funext k
        simp
      rw [map_mul, eval_rename, eval_binomialPoly, hcomp, ← hpeval i m', Fin.cons_zero, mul_comm]

/-- **Numerical polynomials are exactly the functions killed by `d + 1` difference operators.**
This is `lem:deg-difference-lowers-degree` together with `lem:deg-difference-criterion`. -/
theorem isNumericalPolynomial_iff_fwdDiffComp_eq_zero {P : (Fin r → ℤ) → ℤ} :
    IsNumericalPolynomial d P ↔
      ∀ j : Fin (d + 1) → Fin r, fwdDiffComp (fun k ↦ Pi.single (j k) 1) P = 0 :=
  ⟨fun hP j ↦ hP.fwdDiffComp_eq_zero fun k ↦ Pi.single (j k) 1,
    isNumericalPolynomial_of_fwdDiffComp_eq_zero⟩

end Criterion

namespace IsNumericalPolynomial

variable {d s : ℕ} {P : (Fin s → ℤ) → ℤ}

/-- **Substituting a linear map into a numerical polynomial.** If `P` is a numerical polynomial of
total degree at most `d` in `s` variables and `f : ℤ ^ r → ℤ ^ s` is additive, then `P ∘ f` is a
numerical polynomial of total degree at most `d` in `r` variables.

Since `ℤ ^ r` and `ℤ ^ s` are free `ℤ`-modules, an additive `f` is precisely a tuple of `s` integer
linear forms in `r` variables, so this covers every substitution of integer linear forms. This is
`lem:deg-numerical-substitution` of the blueprint. -/
theorem comp_addHom (hP : IsNumericalPolynomial d P) (f : (Fin r → ℤ) →ₙ+ (Fin s → ℤ)) :
    IsNumericalPolynomial d (P ∘ f) :=
  isNumericalPolynomial_of_fwdDiffComp_eq_zero fun j ↦ by
    rw [fwdDiffComp_comp_addHom, hP.fwdDiffComp_eq_zero]
    rfl

/-- **Substituting `m` and `-m` into a numerical polynomial.** If `Q` is a numerical polynomial of
total degree at most `d` in `r + r` variables, then `m ↦ Q (m₁, …, m_r, -m₁, …, -m_r)` is a
numerical polynomial of total degree at most `d` in `r` variables. This is the substitution
performed in the reduction to very ample line bundles in the proof of `thm:deg-snapper` of the
blueprint. -/
theorem comp_append_neg {Q : (Fin (r + r) → ℤ) → ℤ} (hQ : IsNumericalPolynomial d Q) :
    IsNumericalPolynomial d fun m ↦ Q (Fin.append m (-m)) :=
  hQ.comp_addHom <| AddHom.mk (fun m ↦ Fin.append m (-m)) fun m m' ↦ by
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.neg_apply, neg_add]

end IsNumericalPolynomial
