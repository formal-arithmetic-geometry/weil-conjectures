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
- `IsAlgClosed.isCField_zero`: an algebraically closed field is `C₀`.
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
(blueprint: `sk-def-cr`) -/
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
variables has a nontrivial zero. -/
instance IsAlgClosed.isCField_zero [IsAlgClosed K] : IsCField K 0 :=
  sorry

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
