/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.Paper.CompletedTowerCorners
import Sheaf.Paper.StrictTowerExchangeMateNormalization

/-! # Compatibility of the specified strict four towers

Source: blueprint proper base change, tower compatibility
(blueprint: lem-weil-pbc-tower-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- Evaluation gives the specified finite corners and arrows; the rectangle and every
endomorphism compatibility are equations of derived strict-tower morphisms.
Source: blueprint tower compatibility, all clauses
(blueprint: lem-weil-pbc-tower-compatibility).
Proof: exact evaluation of derived reduction is scalar restriction of K_n by its
normalized K-flat counit. Evaluation of tower direct image is the ordinary direct
image derived on K-injective tower models; evaluation preserves those models because
its left adjoint is exact. The ordinary tensor/pullback balancing formula identifies
all four evaluations with the specified corners. Evaluating towerProjection gives
finiteProjection by the normalized scalar and module adjunctions. Thus h and h' give
the displayed arrows. The strict definition v'=h inverse v h' gives the rectangle;
finite-level exchange-tensor coherence identifies its evaluation with the canonical
finite exchange, including any retained witness transport. All maps and comparisons
were formed on strict tower complexes and descend through localization, so their
transition compatibility is retained. Naturality of the original adjunctions and
of reduction gives the displayed endomorphism equality. -/
theorem AdicCoefficientDatum.fourTowers_compatibility [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    (∃ α : ∀ i : Fin 4,
        (reductionTowerDerivedEvaluation Y' (reductionModuleRing Y' (d.completedRing Y')) n).obj
          (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) ≅
        (reductionDerivedRestrict Y' (d.projection Y' n)).obj
          (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i),
      (reductionTowerDerivedEvaluation Y' (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫ (α 1).hom =
        (α 0).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).h.hom ∧
      (reductionTowerDerivedEvaluation Y' (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom ≫ (α 3).hom =
        (α 2).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).h'.hom ∧
      (reductionTowerDerivedEvaluation Y' (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV sq K) ≫ (α 2).hom =
        (α 0).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).v ∧
      (reductionTowerDerivedEvaluation Y' (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV' sq K) ≫ (α 3).hom =
        (α 1).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).v'.hom) ∧
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫ d.towerV' sq K =
      d.towerV sq K ≫ (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom ∧
    (∀ k : K ⟶ K,
      (d.towerPull g).map ((d.towerPush f).map
          ((completedReductionTower X d).map k)) ≫ d.towerV' sq K =
        d.towerV' sq K ≫ (d.towerPush f').map ((d.towerPull g').map
          ((completedReductionTower X d).map k))) := by
  refine ⟨(strictTowerExchangeMateNormalization d sq K hK W).2.1 n, ?_, ?_⟩
  · simp [AdicCoefficientDatum.towerV']
  · intro k
    exact exchangeStrict_naturality d sq k

end AlgebraicGeometry.Scheme
