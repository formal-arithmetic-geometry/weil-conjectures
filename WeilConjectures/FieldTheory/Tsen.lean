/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import WeilConjectures.FieldTheory.Cr
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Tsen's theorem

A field of transcendence degree at most one over an algebraically closed field `k` is
quasi-algebraically closed (`C₁`).

## Main statements

- `RatFunc.isQuasiAlgClosed`: the rational function field `k(t)` is `C₁`.
- `IsQuasiAlgClosed.of_trdeg_le_one`: **Tsen's theorem**.

## Implementation notes

For `k(t)` we follow Lang: a form `F` of degree `d` in `N > d` variables with coefficients in
`k[t]` of degree at most `r` is evaluated on `N`-tuples of polynomials of degree at most `m`.
The vanishing of `F(x(t))` amounts to `d m + r + 1` equations without constant term in the
`N (m + 1)` coefficients of `x(t)`, which have a common nontrivial zero over `k` as soon as
`N (m + 1) > d m + r + 1` (`MvPolynomial.exists_ne_zero_forall_eval_eq_zero`).
-/

@[expose] public section

open MvPolynomial

/-- **Tsen's theorem for `k(t)`.** The rational function field over an algebraically closed
field is quasi-algebraically closed.
(blueprint: `lem-sc-tsen`) -/
instance RatFunc.isQuasiAlgClosed (k : Type*) [Field k] [IsAlgClosed k] :
    IsQuasiAlgClosed (RatFunc k) :=
  sorry

/-- **Tsen's theorem.** A field `K` of transcendence degree at most one over an algebraically
closed field `k` is quasi-algebraically closed. This covers the function field of a curve over
`k` and all its algebraic extensions.
(blueprint: `lem-sc-tsen`, `sk-prop-tsen`) -/
@[stacks 03RD]
theorem IsQuasiAlgClosed.of_trdeg_le_one {K : Type*} [Field K] (k : Type*) [Field k]
    [IsAlgClosed k] [Algebra k K] (h : Algebra.trdeg k K ≤ 1) : IsQuasiAlgClosed K :=
  -- Proof sketch: if `trdeg = 0` then `K` is algebraic over `k`, hence equal to `k`. Otherwise
  -- `K` is algebraic over a subfield `k(t) ≅ RatFunc k`, and `IsQuasiAlgClosed.of_isAlgebraic`
  -- applies.
  sorry
