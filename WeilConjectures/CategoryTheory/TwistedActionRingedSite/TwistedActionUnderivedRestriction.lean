/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorCoherence
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionSpecifiedHomNaturality
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionEvaluationPreservation

/-! # Coherent underived restriction on a specified action site

The specified tensor and Hom comparisons of an action-site presentation satisfy the underived
coherence and evaluation equations.

## References

Stacks Project, Tags 03EK, 03EL and 03EO.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

attribute [local irreducible] SheafOfModules.monoidalCategory sigma
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

/-- The specified action-site tensor and Hom maps satisfy all underived coherence
and evaluation equations. Stacks Project, Tags 03EK, 03EL and 03EO. -/
theorem underived_restriction (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∃ d : RingedForgetTensorTransposition.Underived.{u, u, u, u, u, u}
        P.topology P.coefficient J R U,
      ∀ M N : Modules P.coefficient,
        d.hom.hom.app (op M, N) = (P.hom M N).hom := by
  cases ‹s.functor.IsContinuous J J›
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  obtain ⟨τ, ⟨c⟩, hτ⟩ := tensor_coherence P
  obtain ⟨H, hH⟩ := hom_comparison P
  refine ⟨{ tensor := τ, hom := H, coherence := c, evaluation := ?_ }, hH⟩
  intro M N eB eA hB hA
  simp only [hτ, hH]
  exact specified_evaluation_square P M N eB eA hB hA

end CategoryTheory.TwistedActionRingedSite
