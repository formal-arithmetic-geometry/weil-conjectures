/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.CohenRing
public import Sheaf.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Formal smoothness of field and Cohen power series rings

Source: Stacks Project, More on Algebra, Lemma Tag 07NL, clauses (1) and (3)
(blueprint: lem-weil-pbc-field-cohen-power-series-formally-smooth).
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- Power series over a characteristic-zero field or a Cohen ring are formally smooth
 over the integers for the indicated maximal-ideal adic topology, with a bound on lifts.

Source: Stacks Project, More on Algebra, Lemma Tag 07NL, clauses (1) and (3), and
Lemma Tag 07EC for the bound on the lifted map.
(blueprint: lem-weil-pbc-field-cohen-power-series-formally-smooth)

Proof:
1. Unpack def-weil-pbc-formally-smooth-adic: every ring is uniquely a `ℤ`-algebra,
   and its `ℤ`-algebra maps are precisely ring maps (def-weil-pbc-algebra-hom-quotient).
2. In the Cohen case, apply clause (2) of
   lem-weil-pbc-power-series-cohen-formally-smooth-adic to the square-zero test datum.
3. In the characteristic-zero field case, compose `ℚ → Λ → R → D/J` and lift this
   map to `ℚ → D` by lem-weil-pbc-localization-square-zero-lifting, since `ℚ` is
   the localization of `ℤ` at nonzero integers. This gives compatible `ℚ`-algebra
   structures on `D` and `D/J` (def-weil-pbc-algebra-hom-quotient).
4. Apply clause (1) of lem-weil-pbc-power-series-cohen-formally-smooth-adic over `ℚ`
   to obtain the lift; it is in particular a ring homomorphism over `ℤ`.
5. If `g` kills `m ^ r`, every lift sends `m ^ r` into `J`. Since
   `m ^ (2 * r) = m ^ r * m ^ r`, it sends this ideal into `J ^ 2 = 0`.
   This also supplies continuity, as in def-weil-pbc-formally-smooth-adic. -/
theorem field_cohen_power_series_formally_smooth
    {Λ : Type u} [CommRing Λ] (n : ℕ) (m : Ideal (MvPowerSeries (Fin n) Λ))
    (hΛ : (IsField Λ ∧ CharZero Λ ∧
        m = Ideal.span (Set.range (fun i : Fin n ↦
          (MvPowerSeries.X i : MvPowerSeries (Fin n) Λ)))) ∨
      (∃ p : ℕ, IsCohenRing p Λ ∧
        m = Ideal.span (insert (MvPowerSeries.C (p : Λ))
          (Set.range (fun i : Fin n ↦
            (MvPowerSeries.X i : MvPowerSeries (Fin n) Λ)))))) :
    Algebra.FormallySmoothAdic ℤ (MvPowerSeries (Fin n) Λ) m ∧
      ∀ (D : Type v) [CommRing D] (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : MvPowerSeries (Fin n) Λ →+* D ⧸ J) (r : ℕ), 1 ≤ r →
          (∀ x ∈ m ^ r, g x = 0) →
            ∃ h : MvPowerSeries (Fin n) Λ →+* D,
              (Ideal.Quotient.mk J).comp h = g ∧
                ∀ x ∈ m ^ (2 * r), h x = 0 := by
  sorry

end MvPowerSeries
