/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData

/-! # Assembly of the strict open scalar comparison

Source: Stacks Project, Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Compatible finite-level comparisons assemble to one natural strict-tower
comparison. The assembly is by `NatIso.ofComponents`; successor transition
compatibility supplies the naturality equation and the component formula descends
unchanged to the tower.
Source: Stacks Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-comparison-assembly). -/
theorem openQuotientScalarComparisonAssembly
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (d : ScalarComparisonLevelData l E j o tc sc) :
    Nonempty (ScalarComparison l E j o sc tc) := by
  sorry

end WeilConjectures.OpenTensorQuotient
