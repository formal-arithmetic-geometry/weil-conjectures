/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
public import WeilConjectures.SmoothPurity.IntegralCoherence.SequencePullbackMonoidal

/-! # Strict expression models before derived inverse limit

## References

* Stacks Project, Tags 07A4, 0941 and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

universe t u s i
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}

/-- Normalized strict inverse-image comparisons, including their composition. -/
theorem strictPullbackComparisons
    (W : S → Scheme.{t}) :
    ∃ c : ∀ {a b : S} (f : W a ⟶ W b), PullbackComparison l E f,
      (∀ {a b : S} (f : W a ⟶ W b), Coherent l E f (c f)) ∧
      (∀ {a b d : S} (h : W d ⟶ W a) (f : W a ⟶ W b),
        CompositionLaw l E h f (c f) (c h) (c (h ≫ f))) := by
  exact ⟨fun f ↦ sequenceComparison l E f, fun f ↦ sequenceComparison_coherent l E f,
    fun h f ↦ sequenceComparison_compositionLaw l E h f⟩

end WeilConjectures.IntegralCoherence
