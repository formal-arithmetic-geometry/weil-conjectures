/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData
import Sheaf.SixFunctors.OpenQuotientScalarSystemsComponents
import Sheaf.SixFunctors.OpenQuotientScalarSystemsNaturality

/-! # Strict-system scalar compatibility for an open quotient

Source: Stacks Project, Tags 03DI, 03DJ and 0941.
(blueprint: lem-sf-open-quotient-scalar-system-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The strict-system open extension commutes with coefficient-sequence
restriction. The comparison is assembled from the identity on each extension
summand and is natural in complexes. Source: Stacks Project, Tags 03DI, 03DJ
and 0941. (blueprint: lem-sf-open-quotient-scalar-system-compatibility). -/
theorem openQuotientScalarSystemsCompatibility
    (o : IntegralOpenReduction.Operations l E j) :
    Nonempty ((IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
        forgetSystems l E X ≅
      forgetSystems l E U ⋙ extendTower l E j o)  := by
  obtain ⟨α⟩ := openQuotientScalarSystemsComponents l E j o
  exact ⟨NatIso.ofComponents α
    (openQuotientScalarSystemsNaturality l E j o α)⟩

end WeilConjectures.OpenTensorQuotient
