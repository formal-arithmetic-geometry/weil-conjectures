/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantCohomology
public import Sheaf.RingTheory.DerivedModuleScalarAdjunction

/-! # Formula for the canonical transpose of the lifted transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The canonical transpose is the lifted supplied transpose, up to a comparison iso.
The comparison is the left-adjoint uniqueness isomorphism after transporting the supplied
step adjunction through `finitePerfectAdicAlgebraLiftRestrict`. The displayed equality is
strictly the mate calculation needed for the canonical transpose theorem: expand the lifted
transition, apply the defining unit equation for `leftAdjointUniq`, and use naturality of the
comparison isomorphism. The remaining construction is the universe-lift transport through
the exact scalar restriction comparison.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose-formula). -/
theorem finitePerfectAdicLiftedTransition_canonical_transpose_formula
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
        ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
      RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    letI : (normalizationModuleRestrict q).IsRightAdjoint :=
      ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
    let adj := Adjunction.ofIsRightAdjoint (normalizationModuleRestrict q)
    ∃ e : (normalizationModuleRestrict q).leftAdjoint.obj
          ((finitePerfectAdicAlgebraLift _).obj (T.level (n + 1))) ≅
        (finitePerfectAdicAlgebraLift _).obj
          ((T.stepExtension n).obj (T.level (n + 1))),
      (adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n) =
        e.hom ≫ (finitePerfectAdicAlgebraLift _).map
          ((T.stepAdjunction n).homEquiv _ _ |>.symm (T.transition n)) := by
  sorry

end AlgebraicGeometry.Scheme
