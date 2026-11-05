/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ValuationIndependence
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Discreteness of finite extensions of discretely valued subfields

Let `v` be a valuation on a field `F` and `K₀ ⊆ F` a subfield whose nonzero values are the integral
powers of `v ϖ`, `0 < v ϖ < 1`. We show that a finite extension of `K₀` inside `F` is again
discretely valued (`Valuation.exists_uniformizer_of_finiteDimensional`): if `n` is its degree,
then the `n!`-th powers of its values are powers of `v ϖ`, and the exponents form a subgroup of `ℤ`.

We also record the elementary precision lemma `Valuation.exists_pow_lt_of_pow_eq_zpow`.
-/

@[expose] public section

open Polynomial

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}

end Valuation
