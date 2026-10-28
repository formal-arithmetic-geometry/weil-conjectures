/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibilityGenerator

/-! # Assembly of finite scalar compatibility from finite-level data

Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Compatible finite-level comparisons assemble to a natural isomorphism of
functors. Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility-assembly).
-/
theorem openQuotientScalarFiniteCompatibilityAssembly
    (o : IntegralOpenReduction.Operations l E j)
    (h : ∀ n : ℕ, Nonempty (FiniteScalarLevelData l E j o n)) :
    Nonempty (∀ n : ℕ,
      IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
        scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o) := by
  classical
  refine ⟨fun n ↦ ?_⟩
  let d : FiniteScalarLevelData l E j o n := Classical.choice (h n)
  refine NatIso.ofComponents (fun M ↦ d.level M) ?_
  intro M N f
  exact d.naturality f

end WeilConjectures.OpenTensorQuotient
