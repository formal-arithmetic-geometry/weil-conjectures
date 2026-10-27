/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.SmoothPurityCompletedTowerRoos
public import Sheaf.Paper.DerivedCompleteOnSlices

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
  sorry

end AlgebraicGeometry.ProEtale
