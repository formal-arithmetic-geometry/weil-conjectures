/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! Core valuation-ring existence for a finite extension of a p-adic field.

This is the ring-theoretic and finite-residue-field portion of
`Padic.extension_integers_dvr`; the uniformizer association and factorization clauses
are supplied separately.

Source: Serre, Local Fields, Chapter II, §2, Proposition 3.
(blueprint: lem-weil-l-adic-extension-integers-dvr-core)
-/

@[expose] public section

universe u

namespace Padic

/-- The valuation ring and maximal ideal with all ring-theoretic properties needed before
uniformizer factorization.  This theorem is a strict substatement of
`extension_integers_dvr` and is intended as its ring-theoretic core.

Source: Serre, Local Fields, Chapter II, §2, Proposition 3.
Proof: Equip the finite extension with the extending nonarchimedean norm, apply the
properness criterion for valued fields, and identify the resulting integer ring and
maximal ideal with the absolute-value inequalities.  The DVR and finite-residue-field
properties, together with the elementary unit and fraction-field arguments, give exactly
the displayed conjunction.
(blueprint: lem-weil-l-adic-extension-integers-dvr-core)
-/
theorem extension_integers_dvr_core (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (abv : AbsoluteValue E ℝ)
    (h_ext : ∀ a : ℚ_[l], abv (algebraMap ℚ_[l] E a) = ‖a‖) :
    ∃ O : Subring E, ∃ m : Ideal O,
      (∀ x : E, x ∈ O ↔ abv x ≤ 1) ∧
      (∀ x : O, x ∈ m ↔ abv (x : E) < 1) ∧
      (∀ x : O, IsUnit x ↔ abv (x : E) = 1) ∧
      IsLocalRing O ∧ m.IsMaximal ∧
      (∀ J : Ideal O, J.IsMaximal → J = m) ∧
      IsFractionRing O E ∧
      IsDiscreteValuationRing O ∧ IsPrincipalIdealRing O ∧ m ≠ ⊥ ∧
      (∀ J : Ideal O, J.IsPrime ∧ J ≠ ⊥ ↔ J = m) ∧
      Finite (O ⧸ m) ∧
      (∃ r : ℝ,
        (∃ y : O, y ∈ m ∧ y ≠ 0 ∧ abv (y : E) = r) ∧
        (∀ y : O, y ∈ m → y ≠ 0 → abv (y : E) ≤ r) ∧
        (∀ π : O, Ideal.span ({π} : Set O) = m ↔
          π ≠ 0 ∧ abv (π : E) = r)) ∧
      (∃ π : O, Ideal.span ({π} : Set O) = m) := by
  sorry

end Padic
