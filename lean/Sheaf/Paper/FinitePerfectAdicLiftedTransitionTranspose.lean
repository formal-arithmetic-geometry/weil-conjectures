/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantCohomology

/-! # Transpose of the lifted finite perfect transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The lifted transition has invertible transpose for the derived restriction adjunction.

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-transpose).

The transpose is computed by transporting the normalized transpose of the supplied tower
transition through the coefficient-universe lift and its scalar-restriction comparison.
Both transports are equivalences, so they preserve invertibility. -/
theorem finitePerfectAdicLiftedTransition_transpose_isIso
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ)
    {L : DerivedCategory (ModuleCat.{t + 1}
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) ⥤
      DerivedCategory (ModuleCat.{t + 1}
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))}
    (adj : L ⊣ normalizationModuleRestrict
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) :
    IsIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)) := by
  sorry

end AlgebraicGeometry.Scheme
