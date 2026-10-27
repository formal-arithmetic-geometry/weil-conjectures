/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.CurveRestrictionFiltrationData

/-! # CurveRestrictionLocalPowers

Source: blueprint latest, real-mixed-by-curves, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor (IsoAlgebra)
open Opposite
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

variable (m : ℕ) (hm : 1 ≤ m)
  (C₀ : Over (Spec (.of (D.extensionSubfield m hm))))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (h₀ : C₀ ⟶ constantExtensionModel D m hm X₀) [IsClosedImmersion h₀.left]


variable [IsSeparated C₀.hom]
  [Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
  [Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
    IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x))]

/-- Local residue-degree powers and reality for curve restriction of a constructible
Weil sheaf with its supplied normalized comparison. No filtration or lissity is assumed.
Source: Weil II (1.1.8)--(1.1.10); blueprint real-mixed-by-curves, paragraph 2
(blueprint: lem-zl-curve-restriction-local-powers).

Proof:
Factor the arithmetic map as the closed immersion and constant projection. The
immersion identifies residue fields and sends closed points to closed points.
Constant restriction has local operator equal, under the normalized stalk map,
to the residue-degree power of the original operator. Residue degrees multiply;
the immersion contributes degree one. The finite-field cardinality formula gives
q_z=q_x^f and f is positive. The normalized constant comparison and inverse
pullback compositor give a carrier comparison at a common finite coefficient
stage, by the common-stage Hom calculus, including its inverse and equations.
Thus a ZlCurveFiniteModel exists. Naturality and composition of the normalized
point comparisons identify the composite stalk map with zlCurveFiniteStalkIso.
They intertwine the ordered Weil products and every point transport, giving the
displayed operator equality for every normalized finite model and compatible lift.
Apply power_spectrum_conjugation to the finite-dimensional scalar-extended local
operator and transport characteristic polynomials across this stalk isomorphism.
The all-presentation characterization of sfLocalCharacteristicFactor identifies
these determinants with the local factors. This gives the multiset formula,
including algebraic multiplicities. A conjugation-stable spectrum stays stable
under positive powers, so real local factors stay real at every closed point.
The empty curve has no point conditions; rank zero uses polynomial one. -/
theorem zl_curve_restriction_local_powers
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R)
    (RX : ZlClassicalRealization D l hl Ω X₀)
    (RC : ZlClassicalRealization (constantExtensionDatum D m hm) l hl Ω C₀)
    (c : ZlCurveClassicalPullback D l hl Ω X₀ m hm C₀ h₀ RX RC R)
    (H : sfCommonStageWeilSheaf D l hl X₀ Ω) (iota : Ω ≃+* ℂ) :
    ZlCurveLocalConclusions D l hl Ω X₀ m hm C₀ h₀ R c.underlying H ∧
      (SfIsReal D l hl Ω X₀ iota.toRingHom H →
        SfIsReal (constantExtensionDatum D m hm) l hl Ω C₀ iota.toRingHom
          ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj H)) := by sorry

end WeilConjectures
