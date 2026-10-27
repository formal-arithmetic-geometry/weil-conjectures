/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Existence of normalized scalar compatibility data for an open quotient

Source: Stacks Project, Tags 03DI, 03DA, 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-compatibility-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The finite and strict-system scalar comparisons can be chosen coherently.

The construction uses the identity on extension-by-zero summands at each finite
coefficient level, then assembles these maps over the product of the site with the
coefficient index. The coefficient projection equations identify all finite maps
with the completed scalar action, and the generator formula gives the required
normalization on system units. This is strictly the data portion of the scalar-unit
compatibility theorem; no tensor comparison or unit square is asserted.
Source: Stacks Tags 03DI, 03DA, 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-compatibility-data). -/
theorem openQuotientScalarCompatibilityData
    (o : IntegralOpenReduction.Operations l E j) :
    Nonempty (ScalarCompatibility l E j o) := by
  sorry

end WeilConjectures.OpenTensorQuotient
