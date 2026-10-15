/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! Uniqueness for the unit-times-integer-power factorization in a DVR.

Source: Stacks Project, Algebra, Lemma 00PD.
(blueprint: lem-weil-l-adic-extension-integers-dvr-factorization-unique)
-/

@[expose] public section

namespace Padic

/-- The unit and integer exponent in a DVR fraction-field factorization are unique.

Source: Stacks Project, Algebra, Lemma 00PD.
Proof: compare two expressions after clearing denominators.  The DVR factorization
of nonzero elements and uniqueness of the exponent in a product of powers of an
irreducible force the two integer exponents to agree; cancellation in the domain then
forces the units to agree.
(blueprint: lem-weil-l-adic-extension-integers-dvr-factorization-unique)
-/
theorem extension_integers_dvr_factorization_unique (E : Type*) [Field E] (O : Subring E)
    (m : Ideal O) (hDVR : IsDiscreteValuationRing O) (hmax : m.IsMaximal)
    (hfrac : IsFractionRing O E) :
    ∀ π : O, Ideal.span ({π} : Set O) = m → ∀ x : Eˣ,
      ∀ p q : Oˣ × ℤ,
        (x : E) = ((p.1 : O) : E) * (π : E) ^ p.2 →
        (x : E) = ((q.1 : O) : E) * (π : E) ^ q.2 → p = q := by
  sorry

end Padic
