/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement

/-! # Legacy completed-integral tensor transport

This module retains the pre-reanchor completed/discrete interface for its existing callers.
The current condensed statement of `lem-pur-integral-tensor-transport` is realized in
`Sheaf.Paper.NativeIntegralTensorTransport`; this legacy declaration is not its Lean binding.

Historical source: the Integral twist paragraph of the Cartesian coefficient twists proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Legacy completed/discrete tensor transport, retained for existing callers.
The current condensed transport theorem, including normalized derived finite reduction, is
`AlgebraicGeometry.ProEtale.NativeIntegralTensorTransport.integral_tensor_transport`.
This declaration retains its original statement and outstanding proof obligation.

Specialize normalized semilinear tensor transport to the recorded integral line.
The input comparisons are fixed by their finite projections; the conclusion adds
only the tensor extension, not the coefficient maps or the root-limit map.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-prop-sfb-cartesian-coefficients-twists.proof.md, Integral twist paragraph;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
Historical blueprint association: `lem-pur-integral-tensor-transport` before its condensed
reanchor. The current node is attached to the native declaration named above.

Proof: identify the finite constant comparisons in the coefficient normalization
with the constant-section adjuncts by sheafification uniqueness. Joint monicity
of the coefficient projections then identifies alpha with its normalized ring
comparison. The epsilon square identifies the discrete Z_l scalar structure.
The equations for tau, tested at every root projection, make its adjunct linear
over that base coefficient comparison: finite root comparison is semilinear,
and the root-limit action is coordinatewise. Apply semilinear tensor presentation
transport to the pushout presentation of the completed coefficient ring and to
the root-limit module, transporting through small site models. The abstract
M tensor_D B is canonically the recorded scalar extension B tensor_D M: the
maps on pure tensors reverse the factors and are inverse by the tensor universal
property and sheafification. Forgetting module structure commutes with these
sheafifications and with inverse image. The unit-normalized comparisons identify
the resulting adjunct with the displayed tensor formula. Both completed actions
satisfy the same tensor-pushout action formula, so uniqueness in
purTwistIntegralAction_existsUnique identifies them; semilinearity for all
sections is the corresponding conclusion of tensor presentation transport.
The inverse is the tensor of the inverse root and constant coefficient maps,
so the additive map is an isomorphism. For the empty scheme the same universal
properties apply to zero sheaves. Identity maps and E=Q_l give the usual tensor
unit comparison, with no choice of a primitive root. -/
theorem pur_integral_tensor_transport
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X) [IsIso α]
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l) [IsIso τ]
    (hα : ∀ n : ℕ, α ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (hτ : ∀ n : ℕ,
    τ ≫ limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) =
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)) ≫
          proEtaleRootsOfUnityInverseImageMap h (l ^ (n + 1))) :
    ∃ ρ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E)) ⟶
          (SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E),
      IsIso ρ ∧
    (∀ (V : Y.ProEtᵒᵖ) (b : (purTwistIntegralConstant Y l E).obj.obj V)
          (t : (purTwistZlModule Y l).val.obj V),
        (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
            (purTwistIntegralTensor Y l E V b t) =
          purTwistIntegralTensor X l E ((proEtaleBaseChange h).op.obj V)
            ((proEtaleConstantDirectImageMap h CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
                V b)
            ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) τ).hom.app
              V t)) ∧
      ∀ (V : Y.ProEtᵒᵖ)
          (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj V)
          (t : (purTwistIntegralModule Y l E).val.obj V),
        (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
            (a • t) =
          @id ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
            ((proEtaleBaseChange h).op.obj V))
            ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) •
          @id ((purTwistIntegralModule X l E).val.obj ((proEtaleBaseChange h).op.obj V))
            ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V t) := by
  sorry

end AlgebraicGeometry.Scheme
