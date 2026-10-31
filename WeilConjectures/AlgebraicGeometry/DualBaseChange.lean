/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualBaseChangeFiniteStage
import WeilConjectures.AlgebraicGeometry.DualBaseChangeHigherStages

/-!
# Dual base change

Source: blueprint, sec-six-functors/sk-thm-sf-compatibility,
Dual base change (blueprint: thm-sf-dual-base-change).

The statement is made on the supplied finite-Tor categories.  All maps are the
canonical exchange maps recorded by the datum; no ambient exceptional functor is
introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures


/-- Dual base change for the finite, integral, rational and common-stage meanings of a
six-functor datum. All operations retain the datum's completed, scalar-localized, or
common-stage coefficient conventions.
Source: blueprint, sec-six-functors/sk-thm-sf-compatibility, node thm-sf-dual-base-change
(blueprint: thm-sf-dual-base-change).

Proof: the four stage assertions are proved by the same five-step argument of the
node (composite adjunctions, conjugate of the inverse exchange, mate pasting for
naturality and both pastings, A4 substitution in the proper case). The finite stage is
`dualBaseChangeFiniteStage` (lem-sf-dual-base-change-finite-stage), the integral,
rational and common stages are `dualBaseChangeHigherStages`
(lem-sf-dual-base-change-higher-stages); the theorem is their conjunction. -/
theorem dualBaseChange
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    dualBaseChangeStage S.finite S.finiteCoherence
      (dualBaseChangeFiniteExchange D C E n hn S.toSixFunctorOperationDatum) ∧
    dualBaseChangeStage S.higher.integral S.integralCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.integralExchange Q)) ∧
    dualBaseChangeStage S.higher.rational S.rationalCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.higher.rationalExchange Q)) ∧
    dualBaseChangeStage S.closure.commonStage S.commonCoherence
      (fun Q ↦ dualBaseChangeHigherExchange (S.closure.commonStageExchange Q)) := by
  exact ⟨dualBaseChangeFiniteStage D C E n hn S,
    dualBaseChangeHigherStages D C E n hn S⟩

end WeilConjectures
