/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Normalized tower transition evaluation core -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized tower transition is identified with the coefficient-system transition
through the canonical finite evaluation comparison.
Source: Stacks 0941; the derived restricted-transition calculation.
(blueprint: lem-sf-integral-proper-tower-transition-core).
Proof: unfold the normalized tower and restricted evaluation maps and localize the
sectionwise quotient-transition square; naturality of the restriction composition
comparison gives the displayed equation. -/
theorem normalizedTowerEvaluationTransition (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {Y : Scheme.{u}} (N : coefficientSequenceDerived l E Y) (n : ℕ) :
    (normalizedDVRTowerTransition l E Y D hl n.le_succ).app
        ((coefficientSequenceDerivedRestriction l E Y).obj N) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app N =
    (coefficientRestrictedEvaluationIso l E Y (n + 1)).hom.app N ≫
      (scalarReductionDerivedRestriction l E Y (n + 1)).map
        ((coefficientSequenceDerivedTransition l E Y n.le_succ).app N) ≫
      (normalizedDVRResCompletedComp l E Y D hl n.le_succ).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  sorry

end WeilConjectures.IntegralSystemRealization
