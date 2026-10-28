/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.Paper.CoefficientPullbackUnitCoordinates

/-! # One-step point transport on the finite regular coefficient unit

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
step 4 (blueprint: lem-zl-finite-point-transport-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstantGeometricStalkUnit

/-- One restriction-and-coprojection transport preserves the regular coefficient unit.
Source: current blueprint, sec-zeta-weil/sk-thm-intfactors,
`prop-every-iterate-trace.proof.md`, constant-sheaf clause, reviewed expansion step 4.
(blueprint: lem-zl-finite-point-transport-unit).

Proof: compute on a constant section a of the regular coefficient sheaf at Spec k.
Restriction along geometric Frobenius leaves the value a unchanged. The inverse-image
colimit coprojection and sheafification send it to its constant class. The tensor
comparison inserts the tensor unit, and finiteUnit multiplies back to a by the
adjunction generator formula. Thus the composite on sections is the identity.
Every section is constant by bijectivity of sheafification at the final object of
Spec k. The exact single-complex comparison gives the identity in degree zero.
Naturality of transport and its localization formula remove the chosen representative
used in its definition. The computation includes the quotient with exponent one. -/
theorem finitePointTransport_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (m : ℕ) :
    frobeniusPointTransportFinite D l hl E m
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≫
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          (finiteUnit l E (frobeniusPointIso D).hom m).hom = 𝟙 _ := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
