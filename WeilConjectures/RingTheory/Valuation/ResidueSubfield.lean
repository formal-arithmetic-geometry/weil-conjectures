/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The residue field of a subfield

Let `𝒪` be a valuation subring of a field `Ω` and `S ⊆ Ω` a subfield. The residues of the elements
of `S ∩ 𝒪` form a subfield `𝒪.residueSubfield S` of the residue field of `𝒪`: the residue field of
the restriction of the valuation to `S`.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

variable {𝒪}

end ValuationSubring
