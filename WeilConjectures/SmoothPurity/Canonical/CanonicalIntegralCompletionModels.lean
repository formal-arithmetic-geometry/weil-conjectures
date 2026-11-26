/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Canonical.CanonicalIntegralEvaluationCalculus
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Canonical integral tensor presentations of the completion calculus

Existence of ordinary and derived completion models for the canonical integral evaluation
calculus.

## Implementation details

The integral tensor of the calculus is fixed before constructing the ordinary and derived
comparisons, and no separate existential choice of a different calculus is made.

## References

* [Stacks: Tags 07A6, 09T5, 0D6E, 0941](https://stacks.math.columbia.edu)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletionUnit
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Ordinary and derived completion models for the canonically presented calculus. -/
theorem canonicalIntegralCompletionModels (hl : IsUnit (l : Γ(W, ⊤))) :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S)
      (M : CompletionUnit.OrdinaryModel l E W),
      Nonempty (CompletionUnit.DerivedModel l E W S M) ∧
        (IntegralOnSlice.duality l E W none).closed = S.integralClosed := by
  classical
  let : ∀ x : W, Invertible (l : W.residueField x) := fun x ↦
    (show IsUnit (l : W.residueField x) from by
      simpa only [map_natCast] using
        hl.map ((W.presheaf.germ ⊤ x (by trivial)) ≫ W.residue x).hom).invertible
  obtain ⟨S, coherence, hS⟩ := canonicalIntegralEvaluationCalculus l E W
  obtain ⟨M⟩ := ordinaryModel_exists l E W
  obtain ⟨r, hr⟩ := constantRoosComparison_exists l E W
  obtain ⟨hI, ε, hε, hflat, heval, hhom⟩ :=
    derivedAdjunctionComparison_exists l E W S coherence M
      (termwiseLimitComparison l E W) (termwiseLimitComparison_projection l E W)
      (constantLimitUnit l E W) (constantLimitUnit_normalization l E W)
      (constantLimitUnit_isRightDerived l E W)
  refine ⟨S, coherence, M, ⟨{
    towerLimitComparison := termwiseLimitComparison l E W
    towerLimitComparison_projection := termwiseLimitComparison_projection l E W
    limitUnit := constantLimitUnit l E W
    limitUnit_normalization := constantLimitUnit_normalization l E W
    roos := r
    roos_normalization := hr
    systemUnit := systemLimitUnit l E W M (constantLimitUnit l E W)
    system_isIso := hI
    systemUnit_composition := ?_
    reductionComparison := ε
    reduction_isLeftDerived := hε
    reduction_isIso := hflat
    reduction_evaluation := heval
    hom_normalization := hhom }⟩, hS⟩
  intro I
  rfl

end WeilConjectures
