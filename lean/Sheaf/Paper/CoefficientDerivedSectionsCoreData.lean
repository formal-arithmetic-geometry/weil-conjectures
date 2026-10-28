/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! Transported data for the normalized coefficient-sections core.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941.
(blueprint: lem-coef-derived-sections-core-data)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The scalar, finite-evaluation and total-limit data before their two equations.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; transport through the coefficient
sequence equivalence.
Proof: choose normalized derived sections for the completed coefficient ring and its
quotient tower, transport their scalar and evaluation comparisons through the exact
sequence-site restriction, and transport the ordinary and derived limit comparisons
through the same equivalence. The resulting three fields have exactly the displayed
endpoints.
(blueprint: lem-coef-derived-sections-core-data) -/
structure CoefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W) where
  scalar : CoefficientDerivedSystemScalarCoherence l E W
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t + 1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteSections l E W n
  globalLimit : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t + 1)}

/-- The transported scalar/evaluation/limit data exist under finite tensor normalization.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; extracted construction step of the
normalized coefficient-sections package.
(blueprint: lem-coef-derived-sections-core-data) -/
theorem coefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    Nonempty (CoefficientDerivedSectionsCoreData l E W R) := by
  sorry

end WeilConjectures
