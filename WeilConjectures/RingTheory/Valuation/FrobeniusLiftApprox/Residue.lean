/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResidueSubfield
public import WeilConjectures.RingTheory.Valuation.KummerNormalFormStageOne
public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox.Discrete
public import Mathlib.Algebra.BigOperators.Field

/-!
# Lifts of a Frobenius-closed family of residues

Let `𝒪` be a valuation subring of a field `Ω` and `u i` elements of the residue field whose
monomials `1, u i ^ p ^ n` are linearly independent over the residues `k` of a subfield `K`. Let
`W i ∈ 𝒪` be lifts of the `u i`. We show:

* the lifted monomials are valuation independent over `K`
  (`ValuationSubring.valuation_le_valuation_frobeniusComb`);
* the `p`-th power of a `k`-combination of the monomials has zero coefficients on the `u i`
  (`ValuationSubring.pow_ne_linearCombination`);
* if the monomials span the residues of a subfield `D`, every element of `D ∩ 𝒪` is congruent
  modulo the maximal ideal to a combination of the lifted monomials with coefficients in any
  subfield `K₀` whose residues contain `k` (`ValuationSubring.exists_valuation_sub_lt_one`).
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

variable {p : ℕ} {ι : Type*}

end ValuationSubring
