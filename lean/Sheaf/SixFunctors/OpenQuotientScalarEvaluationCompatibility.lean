/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Evaluation compatibility for open quotient scalar data

Source: Stacks Project, Tags 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-evaluation-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The strict-system comparison and each finite comparison agree under
coefficient evaluation. This is the generator normalization equation, obtained
by evaluating the identity on extension-by-zero summands. Source: Stacks Project,
Tags 0E8I and 0941. (blueprint: lem-sf-open-quotient-scalar-evaluation-compatibility). -/
theorem openQuotientScalarEvaluationCompatibility
    (o : IntegralOpenReduction.Operations l E j)
    (finite : ∀ n : ℕ,
      IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
        scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o)
    (systems : (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
        forgetSystems l E X ≅ forgetSystems l E U ⋙ extendTower l E j o) :
    ∀ (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (n : ℕ) (i : ℤ),
      HEq (((systems.hom.app C).app (op n)).f i)
        ((finite n).hom.app ((coefficientSequenceEvaluation l E U n).obj (C.X i))) := by
  sorry

end WeilConjectures.OpenTensorQuotient
