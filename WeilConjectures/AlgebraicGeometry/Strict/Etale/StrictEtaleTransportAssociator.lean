/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces

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

/-- Tensor associators on ordinary strict systems preserve the composite tensor unit.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-transport-associator).

Proof: the two successive quotient-ring scalar extensions and the scalar extension
along the composite are left adjoint to canonically identified restriction functors.
Use the unique comparison preserving their adjunction units at each coefficient
level, conjugating by the prescribed evaluation isomorphisms. For each successor
transition, precompose both candidate maps with the composite tensor unit. The
transition equations of the three transports and the generator equations for the
coefficient changes give the same map; tensor-adjunction uniqueness gives equality.
Thus the level isomorphisms assemble to an isomorphism of strict systems. Naturality
of the adjunction comparison and of the evaluation isomorphisms gives naturality
for every strict-system morphism. Its unit equation holds by construction. This
also applies to identity maps, zero rings, and non-strict index maps. No derived
category or geometric inverse-image comparison is involved in this conclusion.
-/
theorem strictEtaleOrdinaryTransportAssociator_exists
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {T : Scheme.{u}}
    {P₁ : StrictEtaleEvaluation T O₁ ell₁}
    {P₂ : StrictEtaleEvaluation T O₂ ell₂}
    {P₃ : StrictEtaleEvaluation T O₃ ell₃}
    (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂)
    (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃)
    (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃) :
    ∃ ordinary : U₁₂.ordinary ⋙ U₂₃.ordinary ≅ U₁₃.ordinary,
      ∀ n M,
        (U₁₂.unit (r₂₃ n)).app M ≫ (U₂₃.unit n).app (U₁₂.ordinary.obj M) ≫
          (SheafOfModules.toSheaf.{u + 1} _).map
            ((coefficientEvaluation (J := T.smallEtaleTopology)
              (O := O₃) (ell := ell₃) n).map (ordinary.hom.app M)) =
          (U₁₃.unit n).app M := by sorry

end AlgebraicGeometry
