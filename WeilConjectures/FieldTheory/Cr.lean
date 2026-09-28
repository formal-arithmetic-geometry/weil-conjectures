/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# `Cᵣ` fields

A field `K` is `Cᵣ` if every homogeneous form of degree `d > 0` in more than `d ^ r` variables
has a nontrivial zero over `K`. The case `r = 1` is *quasi-algebraic closure*; it is the one
used in the curve estimates, because by Tsen's theorem the function field of a curve over an
algebraically closed field is `C₁`, and a `C₁` field has trivial Brauer group.

## Main definitions

- `IsCrField`: the class of `Cᵣ` fields.

## Implementation notes

The variables are indexed by `Fin N` rather than by an arbitrary finite type: a class field
quantifying over `σ : Type v` would make `IsCrField` carry a second universe parameter, which
every use site would then have to disambiguate.
-/

@[expose] public section

open MvPolynomial

/-- Let `r ≥ 0`. A field `K` is `Cᵣ` if every homogeneous polynomial form
`F ∈ K[x₁, …, x_N]` of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero in
`K ^ N`, that is, there is `x : Fin N → K` with `x ≠ 0` and `F(x) = 0`.

For `r = 1` this reads: every homogeneous form of degree `d` in `N > d` variables has a
nontrivial zero; a `C₁` field is also called *quasi-algebraically closed*. For `r = 0` the
condition is `N > 1`, so an algebraically closed field is `C₀`, and `C₀` implies `C₁`.
(blueprint: `sk-def-cr`) -/
class IsCrField (K : Type*) [Field K] (r : ℕ) : Prop where
  /-- A homogeneous form of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero. -/
  exists_ne_zero_and_eval_eq_zero (N d : ℕ) (F : MvPolynomial (Fin N) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (hN : d ^ r < N) :
    ∃ x : Fin N → K, x ≠ 0 ∧ eval x F = 0
