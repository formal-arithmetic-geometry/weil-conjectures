/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantCohomology

/-! # Universality of the lifted algebraic transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The coefficient-universe lift of a normalized algebraic transition is universal.

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-universal).

The transpose under the recorded step adjunction is invertible by the normalized
structure field. Universe lifting and the coefficient interchange preserve this
transpose, so the lifted arrow is isomorphic in the structured-arrow category to
the adjunction unit, which is initial.
-/
theorem finitePerfectAdicLiftedTransition_universal
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (finitePerfectAdicLiftedTransition T n))) := by
  sorry

end AlgebraicGeometry.Scheme
