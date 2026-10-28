/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantCohomology
public import Sheaf.RingTheory.DerivedModuleScalarAdjunction

/-! # Canonical transpose of the lifted finite perfect transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The transpose of the lifted transition is invertible for the canonical derived
restriction adjunction. This is the universe-lifted form of the normalized transpose
in the supplied algebraic tower. The proof transports the original transpose through
exact universe lifting and the scalar-restriction comparison.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose). -/
theorem finitePerfectAdicLiftedTransition_canonical_transpose_isIso
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
        ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
      RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    letI : (normalizationModuleRestrict q).IsRightAdjoint :=
      ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
    let adj := Adjunction.ofIsRightAdjoint (normalizationModuleRestrict q)
    IsIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)) := by
  sorry

end AlgebraicGeometry.Scheme
