/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.FiniteCoefficientReductionFlatModel

/-!
# Frobenius coefficient quotient maps

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (2)
(blueprint: def-trf-frobenius-coefficient-reduction-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical constant coefficient quotient map from level `b + 1` to `a + 1`.
Source: blueprint clause (2), coefficient quotient map in the Frobenius reduction
construction (blueprint: def-trf-frobenius-coefficient-reduction-map). -/
def frobeniusReductionRingMap (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b) :
    proEtaleConstantRing X (Padic.coefficientExtensionRing l E (b + 1)) ⟶
      proEtaleConstantRing X (Padic.coefficientExtensionRing l E (a + 1)) :=
  flatModelReductionRingMap l E (a + 1) (b + 1) (Nat.add_le_add_right h 1) X

end WeilConjectures
