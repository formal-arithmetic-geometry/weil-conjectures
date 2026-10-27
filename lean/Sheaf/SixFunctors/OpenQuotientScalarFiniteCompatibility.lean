/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Finite scalar compatibility for an open quotient

Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The finite open-extension functor commutes with scalar restriction at every
coefficient quotient. The comparison is obtained from the identity on the
extension-by-zero summands, transported through the coefficient equivalences.
Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility). -/
theorem openQuotientScalarFiniteCompatibility
    (o : IntegralOpenReduction.Operations l E j) :
    Nonempty (∀ n : ℕ,
      IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
        scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o) := by
  sorry

end WeilConjectures.OpenTensorQuotient
