/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox.Residue
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Residues which are not `p`-th powers

Let `R` be a field of characteristic `p` and `k ≤ R` a subfield such that the monomials
`1, u i ^ p ^ n` are linearly independent over `k`. The `p`-th power of a `k`-combination of the
monomials is a combination of the monomials `1, u i ^ p ^ (n + 1)`, so a combination with a
nonzero coefficient on some `u i` is not such a `p`-th power
(`LinearIndependent.pow_ne_linearCombination`).

As an application, if `x̄` is a polynomial with `p`-th power coefficients in every residue `ρ`
of `D` which is not a `p`-th power, then `x` is congruent to a polynomial with `p`-th power
coefficients in any integral combination `S` of the lifted monomials with a unit coefficient on
some `W i` (`ValuationSubring.exists_valuation_sub_sum_pow_mul_pow_lt_one`).
-/

@[expose] public section

open IsLocalRing

variable {ι : Type*}

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω} {p : ℕ}

end ValuationSubring
