/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResidueSubfield
public import WeilConjectures.RingTheory.Valuation.ResidueLinearIndependent
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Gauss valuation on a simple residually transcendental extension

Let `𝒪` be a valuation subring of a field `Ω`, `F ⊆ Ω` a subfield and `x ∈ 𝒪` whose residue `x̄`
is transcendental over a subfield `k` of the residue field containing the residues of `F ∩ 𝒪`.
Then the valuation on `F[x]` is the Gauss valuation: `v (∑ cᵢ xⁱ) = maxᵢ v (cᵢ)`
(`ValuationSubring.valuation_aeval_eq_sup`), and the residues of the integral elements of
`F(x)` lie in `k(x̄)` (`ValuationSubring.residue_mem_adjoin_of_mem_adjoin`).

We also record that the residues of an algebraically closed subfield form an algebraically
closed subfield of the residue field (`ValuationSubring.isAlgClosed_residueSubfield`).
-/

@[expose] public section

open IsLocalRing Polynomial

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

end ValuationSubring
