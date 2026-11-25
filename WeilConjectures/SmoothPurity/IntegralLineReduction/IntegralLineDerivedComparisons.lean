/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineNormalizedDerivedComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineSupportPreservation

/-! # Derived signed line reduction

## References

* Stacks Project, Tags 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Derived quotient extension of a signed line twist is normalized by balancing,
commutes with the strict transitions, and preserves every uniform support interval. -/
theorem integral_line_derived_comparisons
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (b : PowerComparisons l E X L) (hb : PowerFormula l E X L b) :
    ∃ d : DerivedComparisons l E X L,
      DerivedFormula l E X L b d ∧
      (∀ (m : ℤ) (K : D.{u, u} l E X none) (a z : ℤ),
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a z) →
        ∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((ordinary l E X L m).obj K)) ⊆ Set.Icc a z) := by
  obtain ⟨d, hd⟩ := integral_line_normalized_derived_comparisons l E X L b hb
  refine ⟨d, hd, ?_⟩
  intro m K a z h n i hi
  apply h n
  apply finite_ordinary_support_subset l E X L n m
  intro hzero
  apply hi
  exact hzero.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso ((d m n).app K))

end WeilConjectures.IntegralLineReduction
