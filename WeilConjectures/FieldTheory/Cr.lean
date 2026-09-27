/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# `Cᵣ` fields

A field `K` is `Cᵣ` if every homogeneous form of degree `d > 0` in more than `d ^ r` variables
has a nontrivial zero over `K`. The case `r = 1` is *quasi-algebraic closure*; it is the one
used in the curve estimates, because by Tsen's theorem the function field of a curve over an
algebraically closed field is `C₁`, and a `C₁` field has trivial Brauer group.

## Main definitions

- `IsCr`: the class of `Cᵣ` fields.

## Implementation notes

The variables are indexed by `Fin N` rather than by an arbitrary finite type: a class field
quantifying over `σ : Type v` would make `IsCr` carry a second universe parameter, which every
use site would then have to disambiguate. An application whose variables are naturally indexed
by something else — the reduced-norm form of `lem-sc-c1-brauer-trivial`, indexed by a basis —
has to rename its variables first.

## Main statements

- `IsCr.of_finiteDimensional`: a finite extension of a `C₁` field is `C₁`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

open MvPolynomial

/-- Let `r ≥ 0`. A field `K` is `Cᵣ` if every homogeneous polynomial form
`F ∈ K[x₁, …, x_N]` of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero in
`K ^ N`, that is, there is `x : Fin N → K` with `x ≠ 0` and `F(x) = 0`.

For `r = 1` — the only case used below — this reads: every homogeneous form of degree `d` in
`N > d` variables has a nontrivial zero; a `C₁` field is also called *quasi-algebraically
closed*. For `r = 0` the condition is `N > 1`, so an algebraically closed field is `C₀`, and
`C₀` implies `C₁`.
(blueprint: `def-sc-cr-field`) -/
class IsCr (K : Type*) [Field K] (r : ℕ) : Prop where
  /-- A homogeneous form of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero. -/
  exists_ne_zero_and_eval_eq_zero (N d : ℕ) (F : MvPolynomial (Fin N) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (hN : d ^ r < N) :
    ∃ x : Fin N → K, x ≠ 0 ∧ eval x F = 0

/-- **A finite extension of a `C₁` field is `C₁`.** Given a homogeneous form `F` of degree `d`
in `N > d` variables over `L`, write its variables in a `K`-basis `e₁, …, e_m` of `L` and take
the field norm of `F`: this is a form of degree `m * d` in `m * N > m * d` variables over `K`,
whose nontrivial zeros are exactly the nontrivial zeros of `F`. The proof is `sorry`.

This is the second step of Tsen's theorem `AlgebraicGeometry.isCr_functionField`: the function
field of a curve is a finite extension of a rational function field.
(blueprint: `lem-sc-c1-finite-extension`) -/
theorem IsCr.of_finiteDimensional (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsCr K 1] : IsCr L 1 :=
  sorry
