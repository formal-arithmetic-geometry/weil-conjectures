/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
import all Sheaf.Paper.CompletedDirectImageLimits

/-!
# The source augmentation of completed base change

Source: Stacks Project, Tag 07A7, remark-base-change; strict-augmentation refinement
of the integral-lattice paragraph of blueprint thm-weil-pbc-finite-extension
(blueprint: lem-weil-pbc-completed-source-augmentation-normalization).

The four equations use the actual strict quotient augmentation, pullback/reduction
comparison, projection-formula comparisons and ambient adjunction mate. All arrows
are those of the imported constructions, before taking derived inverse limits.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Strict exchange carries the specified source quotient augmentation. The successive
clauses are j gamma = u, s = F(H) j, naturality of u on the ambient mate, and
F(v') s gamma = F(H') u e. Composition is written in diagrammatic order.
The units and comparisons retain the strict quotient transitions and the finite
etale-origin transports; no inverse of the ambient mate, exchange or unit is used.

Source: Stacks Project, Tag 07A7, remark-base-change; source-comparison refinement of
blueprint thm-weil-pbc-finite-extension, integral-lattice paragraph
(blueprint: lem-weil-pbc-completed-source-augmentation-normalization).

Proof:
1. Apply lem-weil-pbc-profinite-coefficient-inverse-image to the finite quotient rings.
   The projections identify its coefficient comparison with the completed-pullback
   structure map. Its transition equation identifies the entire pulled quotient diagram.
   The normalized comparison of lem-weil-pbc-reduction-pullback-derived-tower therefore
   takes the pulled strict quotient augmentation to the target quotient augmentation.
2. By def-weil-pbc-completed-pullback, gamma is the constant-tower/Rlim unit followed
   by Rlim of the pulled augmentation. Applying Rlim to the preceding strict equation
   gives gamma followed by j equal to the specified completion unit of M.
3. The source comparison of def-weil-pbc-completed-base-change-map is F(h). The strict
   source projection comparison of lem-weil-pbc-strict-tower-exchange-mate-normalization
   is H = tau inverse followed by h. Hence tau followed by H is h as strict maps;
   prop-weil-pbc-rlim-functoriality gives the second equation.
4. The quotient augmentation is natural, by interchange for tensor with the fixed
   quotient-algebra map. The constant-tower/Rlim unit is natural by its adjunction.
   Applying Rlim and composing these two naturality equations gives the third equation.
5. Strict normalization gives H followed by v' equal to R(e) followed by H prime.
   Apply Rlim and substitute the first three equations. This yields the fourth
   equation, using only the already specified inverse of H. All calculations take
   place on strict diagrams and their derived limits; derived evaluation need not
   be faithful, and e, v' and gamma need not be invertible. -/
theorem completedSourceAugmentationNormalization (d : AdicCoefficientDatum A)
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : d.derived X) (_hK : d.TowerComplete X K)
    (_hC : d.TowerComplete Y ((d.push f).obj K))
    (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    (d.ordinaryToCompleted g ((d.push f).obj K) ≫
        (completedRlim Y' (d.completedRing Y')).map
          ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) =
      d.completionUnit Y' ((d.pull g).obj ((d.push f).obj K))) ∧
    ((completedRlim Y' (d.completedRing Y')).map
        (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom =
      (completedRlim Y' (d.completedRing Y')).map
          ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
        (completedRlim Y' (d.completedRing Y')).map
          (exchangeRealizationH (f := f) (g := g) d K).hom) ∧
    (d.completionUnit Y' ((d.pull g).obj ((d.push f).obj K)) ≫
        (completedRlim Y' (d.completedRing Y')).map
          ((completedReductionTower Y' d).map ((d.integralExchange sq).app K)) =
      (d.integralExchange sq).app K ≫
        d.completionUnit Y' ((d.push f').obj ((d.pull g').obj K))) ∧
    (d.ordinaryToCompleted g ((d.push f).obj K) ≫
        (completedRlim Y' (d.completedRing Y')).map
          (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫
        (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) =
      (d.integralExchange sq).app K ≫
        d.completionUnit Y' ((d.push f').obj ((d.pull g').obj K)) ≫
        (completedRlim Y' (d.completedRing Y')).map
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) := by
  set_option backward.isDefEq.respectTransparency false in
    let F := completedRlim Y' (d.completedRing Y')
    let R := completedReductionTower Y' d
    let η : 𝟭 (d.derived Y') ⟶ R ⋙ F :=
      (d.constantRlimAdjunction Y').unit ≫
        Functor.whiskerRight (completedReductionAugmentation d Y') F
    have hj : d.ordinaryToCompleted g ((d.push f).obj K) ≫
        F.map ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) =
          d.completionUnit Y' ((d.pull g).obj ((d.push f).obj K)) := by
      unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
      rw [Category.assoc, ← Functor.map_comp]
      congr 1
      rw [Category.assoc, reduction_augmentation]
      simp only [Iso.inv_hom_id_app_assoc]
    have hH : F.map (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom =
        F.map ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
          F.map (exchangeRealizationH (f := f) (g := g) d K).hom := by
      rw [← F.map_comp]
      congr 1
      change _ = (d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K) ≫
        (d.reductionTowerPullbackIso g).inv.app ((d.push f).obj K) ≫ _
      rw [Iso.hom_inv_id_app_assoc]
      rfl
    have hn := (η.naturality ((d.integralExchange sq).app K)).symm
    change d.completionUnit Y' ((d.pull g).obj ((d.push f).obj K)) ≫
        F.map (R.map ((d.integralExchange sq).app K)) =
      (d.integralExchange sq).app K ≫
        d.completionUnit Y' ((d.push f').obj ((d.pull g').obj K)) at hn
    refine ⟨hj, hH, hn, ?_⟩
    change d.ordinaryToCompleted g ((d.push f).obj K) ≫
        F.map (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫
          F.map (d.towerV' sq K) = _
    rw [hH]
    simp only [Category.assoc]
    rw [reassoc_of% hj, ← F.map_comp]
    rw [(strictTowerExchangeMateNormalization d sq K _hK _W).1]
    simp only [Iso.hom_inv_id_assoc, F.map_comp]
    exact (reassoc_of% hn) (F.map (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom)

end AlgebraicGeometry.Scheme
