/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.FourArrows
public import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.FourCorners
import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality

/-!
# The specified four corners and arrows in the derived category of strict towers

Source: blueprint proper base change, tower compatibility
(blueprint: lem-weil-pbc-tower-compatibility).

## Main statements

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourTowers_compatibility`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme


variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The strict four corner towers, formed before taking Rlim. The third corner uses
ordinary pullback. Source: blueprint tower compatibility
(blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.fourTowerCorners (K : d.derived X) :
    Fin 4 → DerivedCategory (d.towers Y') :=
  ![(d.towerPull g).obj ((completedReductionTower Y d).obj ((d.push f).obj K)),
    (d.towerPull g).obj ((d.towerPush f).obj
      ((completedReductionTower X d).obj K)),
    (completedReductionTower Y' d).obj ((d.push f').obj ((d.pull g').obj K)),
    (d.towerPush f').obj ((d.towerPull g').obj
      ((completedReductionTower X d).obj K))]

/-- The specified strict projection h, including the canonical source identification.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerH (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 :=
  (d.towerPull g).mapIso (asIso (d.towerProjection f K))

/-- The specified strict projection h', followed by the inverse pullback/reduction map.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerH' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  asIso (d.towerProjection f' ((d.pull g').obj K)) ≪≫
    (d.towerPush f').mapIso ((d.reductionTowerPullbackIso g').symm.app K)

/-- The strict reduction of ambient exchange, with the source chi retained.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerV (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 :=
  (d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K) ≫
    (completedReductionTower Y' d).map ((d.integralExchange sq).app K)

/-- The specified strict lift of finite exchange. This is the projection-formula
realization H' R(e) H inverse; equality of its evaluations does not define its lift.
Source: blueprint tower compatibility, as expanded in strict-tower mate normalization
(blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerV' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).inv ≫
    d.towerV sq K ≫ (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom

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
  sorry

end AlgebraicGeometry.Scheme
