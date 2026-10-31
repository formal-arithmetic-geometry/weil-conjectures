/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedProjectionAdjunction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedObjectReconstruction
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerFiniteReduction

/-! # Canonical reconstruction adjunction for completed ell-power towers

Source: latest blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence.proof.md;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: lem-sp-completed-reduction-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The canonical ell-power reduction/limit adjunction and its reconstruction maps.
Source: latest blueprint, normalized equivalence, Adjunction, Unit and Counit paragraphs;
Bhatt--Scholze, Lemma 3.5.7(1)--(5)
(blueprint: lem-sp-completed-reduction-adjunction).

Proof: write ell = unit times pi^e with e positive. The coefficient-ring quotient
isomorphisms identify the ell-power strict system with the subsequence of the pi-power
system at e(n+1). The floor-index exact right extension is right adjoint to subsequence
restriction. Compose its derived Hom bijection with the uniformizer reduction/limit
adjunction of coefficientDerivedSystemEvaluationCalculus. Arithmetic cofinality
identifies the resulting right adjoint with spCompletedTotalLimit, preserving each
projection. Uniqueness of left derived functors and the local tensor-generator formula
for R identify the left adjoint with spCompletedReduction. For a normalized ell-power
tower, ceiling-index left extension gives a normalized pi-power tower. Arithmetic
interpolation and normalized DVR effectivity make its projection-induced finite
comparisons invertible. Those comparisons are the evaluated counit just constructed;
jointly conservative evaluations therefore make the counit invertible. Finally the
actual uniformizer unit on a derived-complete object is invertible by
purNormalizedReconstruction. Projection-preserving arithmetic cofinality and the
quotient-map normalization identify it with the unit of this transported adjunction.
These arguments impose neither constructibility nor boundedness. -/
theorem spCompletedReduction_limitAdjunction
    [∀ x : T, Invertible (l : T.residueField x)]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) :
    ∃ adj : spCompletedReduction l E T D R ⊣ spCompletedTotalLimit l E T D,
      (∀ M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T),
        WeilConjectures.IntegralOnSlice.IsComplete l E T none M →
          IsIso (adj.unit.app M)) ∧
      (∀ C : spDerivedCoefficientTowers l E T D,
        IsSpNormalizedTower l E T D C → IsIso (adj.counit.app C)) := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  let : D.equivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let := WeilConjectures.integralOperationsDerivedCountableProducts l E T
  obtain ⟨adj, hprojection⟩ := spCompletedReduction_projectionAdjunction l E T D R
  have hc (C : spDerivedCoefficientTowers l E T D)
      (hC : IsSpNormalizedTower l E T D C) : IsIso (adj.counit.app C) := by
    have heval (n : ℕ) :
        IsIso ((spDerivedCoefficientEvaluation l E T D n).map (adj.counit.app C)) := by
      obtain ⟨δ, hδ⟩ := spCompletedTotalLimit_roos l E T D C
      have := spTower_projection_finite_reduction l E T D C hC _ _ δ hδ n
      obtain ⟨e, he⟩ := hprojection C n
      rw [he]
      infer_instance
    have : IsIso (D.equivalence.mapDerivedCategory.functor.map (adj.counit.app C)) := by
      apply (SheafOfModules.systemDerivedEvaluation_isIso_iff
        (spCoefficientCommRings l E T) _).2
      intro n
      let := D.evaluationLimits n
      let := D.evaluationColimits n
      let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
        Functor.additive_of_preserves_binary_products _
      exact (NatIso.isIso_map_iff
        (Functor.mapDerivedCategoryCompIso D.equivalence.functor
          (SheafOfModules.systemEvaluation (spCoefficientCommRings l E T) n))
        (adj.counit.app C)).1 (heval n)
    exact isIso_of_reflects_iso (adj.counit.app C) D.equivalence.mapDerivedCategory.functor
  refine ⟨adj, ?_, hc⟩
  intro M hM
  obtain ⟨C, hC, ⟨e⟩⟩ := spCompletedObject_reconstruction l E T D M hM
  have := hc C hC
  have : IsIso (adj.unit.app ((spCompletedTotalLimit l E T D).obj C) ≫
      (spCompletedTotalLimit l E T D).map (adj.counit.app C)) := by
    rw [adj.right_triangle_components]
    exact CategoryTheory.IsIso.id _
  have : IsIso (adj.unit.app ((spCompletedTotalLimit l E T D).obj C)) :=
    IsIso.of_isIso_comp_right _ ((spCompletedTotalLimit l E T D).map (adj.counit.app C))
  have : IsIso (adj.unit.app M ≫
      (spCompletedReduction l E T D R ⋙ spCompletedTotalLimit l E T D).map e.hom) := by
    rw [← adj.unit.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((spCompletedReduction l E T D R ⋙ spCompletedTotalLimit l E T D).map e.hom)

end AlgebraicGeometry.ProEtale
