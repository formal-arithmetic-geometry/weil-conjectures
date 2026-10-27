/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Degree-zero coefficient gamma projection transport

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the H⁰ specialization of `enrichedSequenceProjectionFormula`
(blueprint: lem-coef-derived-system-hom-projection-transport).
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
The H⁰ clause of the enriched sequence projection theorem transports to the
actual coefficient gamma map and its finite mapping-limit projections.

Source: Stacks 07A6, 08JA, 0D6E and 0941, together with
`SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula`.
Proof: take degree zero in the transported enriched projection identity; use the
recorded additive H⁰ Hom equivalences and their naturality, then apply
`H.scalar_hom_zero` to identify the finite scalar adjunct. Naturality of
`S.reductionEvaluation` and the counit projection rewrite the result as the
specified composite in `CoefficientHomProjection`.
(blueprint: lem-coef-derived-system-hom-projection-transport)
-/
theorem coefficientDerivedSystemHomProjectionTransport
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientHomProjection l E W S := by
  sorry

end WeilConjectures
