/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Enriched coefficient gamma projection transport

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the specialization of `enrichedSequenceProjectionFormula` to the coefficient calculus
(blueprint: lem-coef-derived-system-gamma-projection-transport).
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

/--
The enriched sequence projection theorem, transported through the coefficient
sequence-site, gives the finite projection identity for `S.gamma`.

Source: Stacks 07A6, 08JA, 0D6E and 0941, together with
`SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula`.
Proof: identify the coefficient sequence-site with the strict system presentation;
apply the enriched projection formula to the actual reduction adjunction and tensor
comparison; use `D.globalLimit_model`, `D.globalEvaluation_model`, and
`D.scalarSections_model` to transport the derived sections and limit comparisons.
Finally use `H.sections_projection` at the internal-Hom system. The resulting
composition is exactly the displayed `CoefficientGammaProjection` equation,
including the prescribed first-variable reduction comparison.
(blueprint: lem-coef-derived-system-gamma-projection-transport)
-/
theorem coefficientDerivedSystemGammaProjectionTransport
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientGammaProjection l E W S D := by
  sorry

end WeilConjectures
