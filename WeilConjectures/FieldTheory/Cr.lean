/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# `Cᵣ` fields and Tsen's theorem

A field `K` has *property `Cᵣ`* if every homogeneous form of degree `d > 0` in more than
`d ^ r` variables has a nontrivial zero over `K`. The case `r = 1` is *quasi-algebraic
closure*.

## Main definitions

- `IsCField`: the class of fields with property `Cᵣ`.
- `IsQuasiAlgClosed`: quasi-algebraically closed fields, that is, `C₁` fields.

## Main statements

- `IsCField.mono`: property `Cᵣ` implies property `Cₛ` for `r ≤ s`.
- `IsAlgClosed.isCField_zero`: an algebraically closed field is `C₀`, hence `C₁`.
- `IsQuasiAlgClosed.of_trdeg_le_one`: **Tsen's theorem**, a field of transcendence degree at
  most one over an algebraically closed field is `C₁`.
- `IsQuasiAlgClosed.subsingleton_brauerGroup`: the Brauer group of a `C₁` field vanishes.

## Implementation notes

The variables are indexed by `Fin N` rather than by an arbitrary finite type: a class field
quantifying over `σ : Type v` would make `IsCField` carry a second universe parameter, which
every use site would then have to disambiguate.
-/

@[expose] public section

universe u

open MvPolynomial

/-- Let `r ≥ 0`. A field `K` has *property `Cᵣ`* if every homogeneous polynomial form
`F ∈ K[x₁, …, x_N]` of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero in
`K ^ N`, that is, there is `x : Fin N → K` with `x ≠ 0` and `F(x) = 0`.
(blueprint: `sk-def-cr`, `def-sc-cr-field`) -/
class IsCField (K : Type*) [Field K] (r : ℕ) : Prop where
  /-- A homogeneous form of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero. -/
  exists_ne_zero_and_eval_eq_zero {N d : ℕ} (F : MvPolynomial (Fin N) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (hN : d ^ r < N) :
    ∃ x : Fin N → K, x ≠ 0 ∧ eval x F = 0

/-- A field is *quasi-algebraically closed* if it is `C₁`: every homogeneous form of degree
`d > 0` in `N > d` variables has a nontrivial zero. -/
abbrev IsQuasiAlgClosed (K : Type*) [Field K] : Prop := IsCField K 1

variable {K : Type*} [Field K]

/-- Property `Cᵣ` implies property `Cₛ` for `r ≤ s`. -/
theorem IsCField.mono {r s : ℕ} (hrs : r ≤ s) [h : IsCField K r] : IsCField K s where
  exists_ne_zero_and_eval_eq_zero F hF hd hN :=
    h.exists_ne_zero_and_eval_eq_zero F hF hd ((Nat.pow_le_pow_right hd hrs).trans_lt hN)

/-- An algebraically closed field is `C₀`: a homogeneous form of positive degree in at least two
variables has a nontrivial zero.
(blueprint: `sk-def-cr`) -/
instance IsAlgClosed.isCField_zero [IsAlgClosed K] : IsCField K 0 where
  exists_ne_zero_and_eval_eq_zero {N d} F hF hd hN := by
    rw [pow_zero] at hN
    let i₀ : Fin N := ⟨0, by omega⟩
    let i₁ : Fin N := ⟨1, hN⟩
    have h₀₁ : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
    -- the point `(a, b, 0, …, 0)` and the restrictions of `F` to two affine lines through it
    let v : K → K → Fin N → K := fun a b i =>
      if i = i₀ then a else if i = i₁ then b else 0
    have hv₀ (a b : K) : v a b i₀ = a := by simp [v]
    have hv₁ (a b : K) : v a b i₁ = b := by simp [v, h₀₁]
    have heval (g : Fin N → Polynomial K) (t : K) :
        (aeval g F).eval t = eval (fun i => (g i).eval t) F := by
      rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
      rfl
    let p : Polynomial K :=
      aeval (fun i => if i = i₀ then 1 else if i = i₁ then Polynomial.X else 0) F
    let q : Polynomial K :=
      aeval (fun i => if i = i₀ then Polynomial.X else if i = i₁ then 1 else 0) F
    have hp (t : K) : p.eval t = eval (v 1 t) F := by
      rw [heval]
      exact congrArg (fun x => eval x F) (funext fun i => by simp only [v]; split_ifs <;> simp)
    have hq (t : K) : q.eval t = eval (v t 1) F := by
      rw [heval]
      exact congrArg (fun x => eval x F) (funext fun i => by simp only [v]; split_ifs <;> simp)
    by_cases hroot : ∃ t, p.IsRoot t
    · obtain ⟨t, ht⟩ := hroot
      refine ⟨v 1 t, fun h => by simpa [hv₀] using congrFun h i₀, ?_⟩
      rw [← hp]
      exact ht
    -- otherwise `F (1, t, 0, …, 0)` is a constant `c`, so `F (s, 1, 0, …, 0) = c * s ^ d`
    push Not at hroot
    have hdeg : p.degree = 0 := by
      by_contra h
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p h
      exact hroot t ht
    obtain ⟨c, hc⟩ : ∃ c, p = Polynomial.C c :=
      ⟨_, Polynomial.eq_C_of_degree_eq_zero hdeg⟩
    have hqeq : q = Polynomial.C c * Polynomial.X ^ d := by
      refine Polynomial.eq_of_infinite_eval_eq _ _
        ((Set.finite_singleton (0 : K)).infinite_compl.mono fun s (hs : s ≠ 0) => ?_)
      have hvs : v s 1 = fun i => s * v 1 s⁻¹ i := by
        ext i; simp only [v]; split_ifs <;> simp [hs]
      have hFs : eval (fun i => s * v 1 s⁻¹ i) F = s ^ d * eval (v 1 s⁻¹) F :=
        hF.eval₂Hom_const_mul (RingHom.id K) s _
      rw [Set.mem_ofPred_eq, hq, hvs, hFs, ← hp, hc]
      simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      ring
    refine ⟨v 0 1, fun h => by simpa [hv₁] using congrFun h i₁, ?_⟩
    rw [← hq, hqeq]
    simp [hd.ne']

/-- An algebraically closed field is quasi-algebraically closed, since `C₀` implies `C₁`.
(blueprint: `sk-def-cr`) -/
instance IsAlgClosed.isQuasiAlgClosed [IsAlgClosed K] : IsQuasiAlgClosed K :=
  IsCField.mono zero_le_one

/-- **Tsen's theorem.** A field `K` of transcendence degree at most one over an algebraically
closed field `k` is quasi-algebraically closed. This covers the function field of a curve over
`k` and all its algebraic extensions.
(blueprint: `sk-prop-tsen`) -/
@[stacks 03RD]
theorem IsQuasiAlgClosed.of_trdeg_le_one (k : Type*) [Field k] [IsAlgClosed k] [Algebra k K]
    (h : Algebra.trdeg k K ≤ 1) : IsQuasiAlgClosed K :=
  -- Proof sketch: the rational function field `k(t)` is `C₁` by a dimension count on tuples of
  -- polynomials of bounded degree, and a finite extension of a `C₁` field is `C₁` by a
  -- norm-form argument. The algebraic case follows by writing `K` as a union of finite
  -- extensions of `k` resp. `k(t)`.
  sorry

/-- The Brauer group of a quasi-algebraically closed field vanishes: every central simple
algebra over `K` is a matrix algebra.
(blueprint: `sk-prop-tsen`) -/
theorem IsQuasiAlgClosed.subsingleton_brauerGroup (K : Type u) [Field K] [IsQuasiAlgClosed K] :
    Subsingleton (BrauerGroup.{u, u} K) :=
  -- Proof sketch: the reduced norm of a central division algebra of degree `d > 1` over `K` is
  -- a form of degree `d` in `d ^ 2 > d` variables, so it would have a nontrivial zero.
  sorry
