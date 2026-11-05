/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.KummerNormalForm
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms, stage 1: terms of value at least `v p`

We continue the setting of `WeilConjectures.RingTheory.Valuation.KummerNormalForm`. Let
`m : Option (ι × ℕ) → Ω` be the lifted Frobenius monomials (`m none = 1`,
`m (some (i, n)) = w i ^ p ^ n`). In stage 1 of the Kummer normal form, a `1`-unit `u ∈ L₁` with
`u ∈ L₂ ^ p`, congruent modulo `{v < v p}` to a combination of the monomials with coefficients in
a *discretely valued* subfield `K* ≤ K`, is multiplied by `p`-th powers of `L₁` until
`v (u - 1) < v p` (`exists_valuation_div_pow_sub_one_lt`).

The leading terms of value `μ ≥ v p` are `p`-th powers of monomials (the residual hypothesis
`hres1`), hence cancelled by dividing by `(1 + c) ^ p` for an explicit `c ∈ L₁`, up to terms of
value `< v p` and products of monomials, which are re-expanded (`hprod`). The value `μ` takes
finitely many values in the discrete value group of `K*`, so the process terminates.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation Ω Γ₀} {p : ℕ} {ι : Type*}

variable (p) {w : ι → Ω}

namespace IsFrobeniusApprox

variable {p} {S : Subfield Ω}

end IsFrobeniusApprox

