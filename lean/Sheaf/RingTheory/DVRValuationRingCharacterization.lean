/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F1
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The values of ring elements and uniformizers in a DVR

Source: Stacks Project, Algebra, Definition 00IE
(blueprint: lem-sc-dvr-valuation-ring-characterization).
-/

@[expose] public section

universe u₁ v₁

namespace IsDiscreteValuationRing

/-- The adic valuation of a DVR is nonnegative on its nonzero elements,
and gives a uniformizer value one and its inverse value minus one.
Source: Stacks Project, Algebra, Definition 00IE.
(blueprint: lem-sc-dvr-valuation-ring-characterization)

Proof: The maximal-ideal adic valuation is nonnegative on elements of the DVR
by `valuation_le_one`. A generator of the maximal ideal has normalized value
one, by the uniformizer lemmas for `IsDiscreteValuationRing` and
`HeightOneSpectrum`. The normalized additive valuation is
`-WithZero.log` of this maximal-ideal adic valuation, as in the convention
used by `lem-sc-dvr-tensor-surjective-negative-valuation`. Thus a uniformizer
has value one. Finally, multiplicativity applied to `t * t⁻¹ = 1` gives value
minus one for the inverse; `t ≠ 0` because the maximal ideal is nonzero.
-/
theorem dvr_valuation_ring_characterization (B : Type u₁) (K : Type v₁)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    [Algebra B K] [IsFractionRing B K] :
    (∀ b : B, b ≠ 0 → 0 ≤ -WithZero.log
      ((maximalIdeal B).valuation K (algebraMap B K b))) ∧
      (∀ t : B, IsLocalRing.maximalIdeal B = Ideal.span {t} →
        -WithZero.log ((maximalIdeal B).valuation K (algebraMap B K t)) = 1 ∧
          -WithZero.log ((maximalIdeal B).valuation K (algebraMap B K t)⁻¹) = -1) := by
  sorry

end IsDiscreteValuationRing
