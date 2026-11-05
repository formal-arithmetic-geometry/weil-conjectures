/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.RingTheory.Valuation.KummerNormalForm
import Mathlib.Tactic.FieldSimp

/-!
# Hensel's lemma for Kummer equations of exponent `p` in a subfield

Let `Ω` be an algebraically closed field, `𝒪` a valuation subring of `Ω` and `N` a subfield of
`Ω` over which `Ω` is algebraic, such that every automorphism of `Ω/N` maps `𝒪` into itself.
Let `p` be a prime with `0 < v(p) < 1` and `ϖ ∈ N` with `ϖ ^ (p - 1) = -p`.

* `ValuationSubring.exists_pow_eq_one_add`: if `x ∈ N` is negligible, i.e.
  `v(x) ^ (p - 1) ≤ v(p) ^ p`, and the Artin–Schreier equation `n ^ p - n = x / ϖ ^ p` has a
  residual solution in `N ∩ 𝒪`, then `1 + x` is a `p`-th power in `N`.

The substitution `y = 1 + ϖ Z` transforms `y ^ p = 1 + x` into the equation
`(Z + ϖ⁻¹) ^ p = (1 + x) / ϖ ^ p`, which is congruent to `Z ^ p - Z = x / ϖ ^ p` modulo the
maximal ideal of `𝒪`.
-/

@[expose] public section

open Polynomial

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

end ValuationSubring
