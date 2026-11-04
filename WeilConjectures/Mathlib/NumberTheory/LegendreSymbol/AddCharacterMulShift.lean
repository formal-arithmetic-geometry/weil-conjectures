/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Additive characters of a finite field are shifts of a primitive one

Additive characters with values in a field are linearly independent (Dedekind's lemma), so a
finite group `G` has at most `#G` of them. Since the shifts `x ↦ ψ (a x)` of a primitive
character `ψ` of a finite field `F` are pairwise distinct, every character of `F` is such a
shift.

## Main statements

- `AddChar.linearIndependent_coe`: additive characters with values in a field are linearly
  independent.
- `AddChar.exists_mulShift_eq_of_isPrimitive`: every additive character of a finite field is a
  multiplicative shift of a given primitive one.
-/

@[expose] public section

namespace AddChar

variable {G K : Type*} [AddMonoid G] [Field K]

/-- **Dedekind's lemma for additive characters**: distinct additive characters with values in a
field are linearly independent. -/
theorem linearIndependent_coe : LinearIndependent K ((⇑) : AddChar G K → G → K) :=
  (linearIndependent_monoidHom (Multiplicative G) K).comp
    (fun φ : AddChar G K ↦ toMonoidHomEquiv φ) toMonoidHomEquiv.injective

/-- A finite group has finitely many additive characters with values in a field. -/
instance instFinite [Finite G] : Finite (AddChar G K) :=
  have := Fintype.ofFinite G
  linearIndependent_coe.finite

/-- A finite group has at most as many additive characters with values in a field as elements. -/
theorem natCard_le [Finite G] : Nat.card (AddChar G K) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (AddChar G K)
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    (linearIndependent_coe (G := G) (K := K)).fintype_card_le_finrank

/-- Every additive character of a finite field `F` with values in a field is a multiplicative
shift `x ↦ ψ (a x)` of a given primitive character `ψ`. -/
theorem exists_mulShift_eq_of_isPrimitive {F : Type*} [Field F] [Finite F] {ψ : AddChar F K}
    (hψ : ψ.IsPrimitive) (φ : AddChar F K) : ∃ a : F, ψ.mulShift a = φ :=
  ((to_mulShift_inj_of_isPrimitive hψ).bijective_of_nat_card_le natCard_le).2 φ

end AddChar
