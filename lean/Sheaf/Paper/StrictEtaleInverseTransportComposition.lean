/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.EtaleCoefficientTransportInterfaces

/-! # Normalized coefficient transport composition

Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- Normalized geometric inverse-image squares compose through tensor associators.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-inverse-transport-composition).

Proof: form the pasted ordinary inverse-image square. Precompose it at coefficient
level n with the two tensor units. The tensor-unit equations of AT and AS replace
the successive units by the composite unit. Apply the normalization equations of
the two inverse-image squares in succession. Both this map and the single square
then equal the geometric pullback of the same unit. The scalar adjunction makes
precomposition with that unit injective on module morphisms, and forgetting to set
sheaves is faithful, so the ordinary squares agree levelwise. Strict-system
morphisms are determined by their components, giving equality on entire systems.
Apply the complex functor and localization. Substitute the representative equations
of the three inverse-image squares and of AT and AS, and cancel their factorization
isomorphisms. Equality on localized representatives implies equality by the
localization universal property. This gives the equation at every derived object;
no faithfulness of derived evaluation is used.
-/
theorem strictEtaleInverseTransport_composition
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT₁ : StrictEtaleEvaluation T O₁ ell₁}
    {PT₂ : StrictEtaleEvaluation T O₂ ell₂}
    {PT₃ : StrictEtaleEvaluation T O₃ ell₃}
    {PS₁ : StrictEtaleEvaluation S O₁ ell₁}
    {PS₂ : StrictEtaleEvaluation S O₂ ell₂}
    {PS₃ : StrictEtaleEvaluation S O₃ ell₃}
    {UT₁₂ : StrictEtaleCoefficientTransport a T PT₁ PT₂}
    {UT₂₃ : StrictEtaleCoefficientTransport b T PT₂ PT₃}
    {UT₁₃ : StrictEtaleCoefficientTransport (a.comp b) T PT₁ PT₃}
    {US₁₂ : StrictEtaleCoefficientTransport a S PS₁ PS₂}
    {US₂₃ : StrictEtaleCoefficientTransport b S PS₂ PS₃}
    {US₁₃ : StrictEtaleCoefficientTransport (a.comp b) S PS₁ PS₃}
    {A₁ : StrictEtaleOrdinaryImage O₁ ell₁ g}
    {A₂ : StrictEtaleOrdinaryImage O₂ ell₂ g}
    {A₃ : StrictEtaleOrdinaryImage O₃ ell₃ g}
    {D₁ : CoefficientDerivedImage A₁.inverse A₁.rightSystem A₁.systemAdj}
    {D₂ : CoefficientDerivedImage A₂.inverse A₂.rightSystem A₂.systemAdj}
    {D₃ : CoefficientDerivedImage A₃.inverse A₃.rightSystem A₃.systemAdj}
    (V₁₂ : StrictEtaleInverseTransport UT₁₂ US₁₂ A₁ A₂ D₁ D₂)
    (V₂₃ : StrictEtaleInverseTransport UT₂₃ US₂₃ A₂ A₃ D₂ D₃)
    (V₁₃ : StrictEtaleInverseTransport UT₁₃ US₁₃ A₁ A₃ D₁ D₃)
    (AT : StrictEtaleTransportComposition UT₁₂ UT₂₃ UT₁₃)
    (AS : StrictEtaleTransportComposition US₁₂ US₂₃ US₁₃) (K) :
    D₃.inverse.map (AS.derived.hom.app K) ≫ V₁₃.derived.hom.app K =
      V₂₃.derived.hom.app (US₁₂.derived.obj K) ≫
        UT₂₃.derived.map (V₁₂.derived.hom.app K) ≫
          AT.derived.hom.app (D₁.inverse.obj K) := by sorry

end AlgebraicGeometry
