/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Simple roots with a residual approximation in a subfield

Let `Ω` be an algebraically closed field, `𝒪` a valuation subring of `Ω` and `N` a subfield of
`Ω` over which `Ω` is algebraic, such that every automorphism of `Ω/N` maps `𝒪` into itself.

* `ValuationSubring.mem_of_isRoot_of_valuation_sub_lt_one`: if `f` has coefficients in `N ∩ 𝒪`,
  `α` is a root of `f` with `f'(α)` a unit of `𝒪`, and `α` is congruent modulo the maximal ideal
  of `𝒪` to an element of `N ∩ 𝒪`, then `α ∈ N`.
* `ValuationSubring.exists_pow_sub_self_eq`: Artin–Schreier equations with a residual solution
  in `N ∩ 𝒪` have a solution in `N`.
* `ValuationSubring.exists_pow_eq`: `ℓ`-th roots of units of `N ∩ 𝒪` with a residual root in
  `N ∩ 𝒪` exist in `N` when `ℓ` is invertible in the residue field.

Membership in the maximal ideal is expressed as `𝒪.valuation x < 1`, and units of `𝒪` as
`𝒪.valuation x = 1`.
-/

@[expose] public section

open Polynomial

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

end ValuationSubring
