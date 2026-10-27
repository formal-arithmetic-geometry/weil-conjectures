/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel

/-! # Full faithfulness of component inverse image on abelian sheaves
Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2).
(blueprint: lem-zl-component-inverse-fully-faithful).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The component inverse image is fully faithful for a w-contractible affine base.
Source: HRS Proposition 4.3(1), proof and (4.2)
(blueprint: lem-zl-component-inverse-fully-faithful).

Proof: the adjunction unit is an isomorphism. Evaluate it on an extremally disconnected
profinite test E over π₀(T). The corresponding relative test scheme T_E is affine and
w-contractible, its connected-component quotient is E, and every finite qcqs covering
splits after a clopen partition. The Kan-extension formula therefore evaluates inverse
image at T_E as the original abelian sheaf at E. The adjunction unit is the identity
under this formula, since its Kan coprojection is restriction along id_E. Extremally
disconnected tests cover every profinite test by Stonean presentations. Consequently
the unit is locally bijective, hence an isomorphism of sheaves. An adjunction with
invertible unit has fully faithful left adjoint. The empty test has zero abelian
sections by the empty-cover sheaf condition, so the same argument includes T empty. -/
theorem component_inverse_fully_faithful (T : Scheme.{u}) [IsAffine T]
    [IsWContractibleRing Γ(T, ⊤)]
    [(componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)] :
    Nonempty (componentInverse T).FullyFaithful := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
