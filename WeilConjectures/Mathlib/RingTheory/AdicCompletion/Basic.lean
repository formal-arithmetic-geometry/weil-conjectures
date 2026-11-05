/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adically complete rings and their towers of quotients

For an ideal `I` of a commutative ring `R`, the quotient maps `R ⟶ R ⧸ Iⁿ⁺¹` exhibit an
`I`-adically complete ring as the limit of the tower of its quotients: compatible families of
residues lift (`IsPrecomplete.exists_mk_eq_of_factor_eq`), uniquely
(`IsHausdorff.eq_zero_of_forall_mk_eq_zero`).
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

