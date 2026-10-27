/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ConstructibleProjectionMates
import Sheaf.Paper.CompactSupportProjectionFiniteStages
import Sheaf.Paper.CompactSupportProjectionIntegralStages
import Sheaf.Paper.CompactSupportProjectionFieldStages

/-!
# Coherence laws of the compact-support projection maps

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence, statement and proof
(blueprint: prop-sf-pf-coherence).

The structural laws of the projection maps (naturality, compactification independence,
composition, pentagon and the proper identification) at every coefficient stage of a
six-functor operation datum. In the blueprint the projection formula
(fix-prop-projection-formula) uses these laws; here they are proved from the stage-law
lemmas alone, without the invertibility of the projection maps.

## Main statements

* `compactSupportProjection_coherenceLaws`: the laws at the finite, integral, rational,
  common and finite-level stages.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The projection maps of a six-functor operation datum satisfy the coherence laws at all
coefficient stages: finite, integral, rational, common, and the finite levels of the
integral normalizations.

Source: current blueprint prop-sf-pf-coherence, structural clauses
(blueprint: prop-sf-pf-coherence).

Proof: the finite stages are the mate calculus of the finite compact-support projection
(lem-sf-projection-finite-stage-laws: unit/counit naturality, mate pasting for composition
and the pentagon, refinement comparisons, the identity open compactification for proper
maps). The integral stage transports these through the coherent derived systems
(lem-sf-projection-integral-stage-laws), and rationalization and the common stage carry
them further (lem-sf-projection-field-stage-laws). No invertibility of the projection
maps is used. -/
theorem compactSupportProjection_coherenceLaws
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) :
    CompactSupportFiniteProjection.Laws S.toSixFunctorFiniteOperations ∧
    CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain ∧
    CompactSupportProjectionLaws S.higher.rational S.higher.rationalTensor
      S.higher.rationalExchange (fun _ _ ↦ True) ∧
    CompactSupportProjectionLaws S.closure.commonStage S.closure.commonStageTensor
      S.closure.commonStageExchange (fun _ _ ↦ True) ∧
    (∀ m : ℕ, CompactSupportFiniteProjection.Laws
      (S.integralNormalization.finiteLevels m)) ∧
    ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).integral
        (S.closure.coefficientStages E₀).integralTensor
        (S.closure.coefficientStages E₀).integralExchange
        (fun X K ↦ finiteTorConstructibleIntegral C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left K.obj) ∧
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange (fun _ _ ↦ True) ∧
      ∀ m : ℕ, CompactSupportFiniteProjection.Laws
        ((S.coefficientIntegralNormalization E₀).finiteLevels m) := by
  obtain ⟨hf, hfm, hfe⟩ := compactSupportProjectionFormula_finiteStages S
  obtain ⟨hi, hie⟩ := compactSupportProjectionFormula_integralStages S
  obtain ⟨hr, hc, hre⟩ := compactSupportProjectionFormula_fieldStages S
  exact ⟨hf, hi, hr, hc, hfm, fun E₀ ↦ ⟨hie E₀, hre E₀, hfe E₀⟩⟩

end WeilConjectures
