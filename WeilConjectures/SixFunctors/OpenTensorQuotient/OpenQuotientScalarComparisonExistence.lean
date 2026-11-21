/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonAssembly

/-! # Existence of the strict scalar comparison for an open quotient

## References

* [Stacks, Tag 0E8I]
* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A normalized finite tensor comparison lifts to an isomorphism of strict scalar
quotient towers once scalar compatibility data are fixed. This supplies only the
comparison object, not the scalar-adjunction unit equation. -/
theorem openQuotientScalarComparisonExistence
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o) :
    Nonempty (ScalarComparison l E j o sc tc) := by
  obtain ⟨d⟩ := openQuotientScalarComparisonLevelData l E j o tc sc
  exact openQuotientScalarComparisonAssembly l E j o tc sc d

end WeilConjectures.OpenTensorQuotient
