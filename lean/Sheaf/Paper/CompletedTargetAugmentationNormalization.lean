/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

/-!
# Target augmentation of completed base change

Source: Stacks Project, Tag 0A07, lemma-Rf-commutes-with-Rlim, and Equation 0B56,
equation-projection-formula-map; strict-augmentation refinement of the integral-lattice
paragraph of blueprint thm-weil-pbc-finite-extension
(blueprint: lem-weil-pbc-completed-target-augmentation-normalization).

The three identities use the specified quotient augmentation, its completed-pullback
unit, the counit-tensor projection mate and the canonical direct-image/Rlim comparison.
The final statement identifies their occurrence in the completed base-change map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A]

/-- The actual completed-pullback unit is preserved by reduction/pullback and by the
projection/direct-image/limit comparisons. In diagrammatic order the three equations
are gamma followed by F(t) = u, u followed by F(h) = G(u) followed by c, and
u followed by F(h followed by G(t inverse)) = G(gamma) followed by c_Q.
Only t is inverted. No properness, completeness of the ordinary pullback or its direct
image, or invertibility of either the projection mate or gamma is assumed.

Source: Stacks Project, Tag 0A07 and Equation 0B56; agent strict-augmentation refinement
(blueprint: lem-weil-pbc-completed-target-augmentation-normalization).

Proof:
1. Apply lem-weil-pbc-profinite-coefficient-inverse-image to the finite quotients for
   h and p. The coefficient identifications preserve projections and transitions.
   def-weil-pbc-proetale-operations gives exact ordinary and termwise module pullbacks.
2. By def-weil-pbc-completed-pullback, gamma is F of the pulled quotient augmentation
   after the constant-tower unit. The representative-normalized t of
   lem-weil-pbc-reduction-pullback-derived-tower carries that augmentation to i_E0.
   Functoriality of F gives the first equation.
3. lem-weil-pbc-constant-tower-pushforward-normalization identifies F(chi) lambda_N
   with c_Delta G(lambda_E0). The constant-limit identifications are the inverses
   of the same constant-tower units used in the definition of gamma.
4. Apply F to the strict equation h i_N = G_Tow(i_E0) chi of
   lem-weil-pbc-augmented-diagram-projection-mate and precompose with lambda_N.
   Substitute step 3 and use naturality of the actual comparison c at i_E0.
   This gives the second equation. The comparison of prop-weil-pbc-direct-image-limits
   is normalized by the common underived composite; its naturality is also explicit in
   lem-weil-ringed-tower-pushforward-limit-comparison.
5. Expand H prime as h followed by G_Tow(t inverse). Apply naturality of the same c
   at t inverse, then step 2 after F(t inverse). This gives the third equation.
   Neither completeness of E0 or N nor any inverse of h or gamma enters the argument. -/
theorem completedTargetAugmentationNormalization (d : AdicCoefficientDatum A)
    {U V W : Scheme.{t}} (h : U ⟶ V) (p : U ⟶ W)
    (L : d.derived V) (_hL : d.TowerComplete V L) :
    (d.ordinaryToCompleted h L ≫
        (completedRlim U (d.completedRing U)).map
          ((d.reductionTowerPullbackIso h).hom.app L) =
      d.completionUnit U ((d.pull h).obj L)) ∧
    (d.completionUnit W ((d.push p).obj ((d.pull h).obj L)) ≫
        (completedRlim W (d.completedRing W)).map
          (d.towerProjection p ((d.pull h).obj L)) =
      (d.push p).map (d.completionUnit U ((d.pull h).obj L)) ≫
        (d.directImageRlimIso p).hom.app
          ((completedReductionTower U d).obj ((d.pull h).obj L))) ∧
    (d.completionUnit W ((d.push p).obj ((d.pull h).obj L)) ≫
        (completedRlim W (d.completedRing W)).map
          (d.towerProjection p ((d.pull h).obj L) ≫
            (d.towerPush p).map ((d.reductionTowerPullbackIso h).inv.app L)) =
      (d.push p).map (d.ordinaryToCompleted h L) ≫
        (d.directImageRlimIso p).hom.app
          ((d.towerPull h).obj ((completedReductionTower V d).obj L))) := by
  dsimp only [AdicCoefficientDatum.completedPull, Functor.comp_obj] at *
  have ht : d.reductionTowerPullbackIso h = stratumReductionIso d h := by
    apply (completedReductionPullbackIso_existsUnique d h).unique
    · exact (completedReductionPullbackIso_existsUnique d h).choose_spec.1
    · exact (stratumReductionIso_exists d h).exists.choose_spec
  have ha := stratumReduction_augmentation d h L
  rw [← ht] at ha
  have hu : d.ordinaryToCompleted h L ≫
      (completedRlim U (d.completedRing U)).map
        ((d.reductionTowerPullbackIso h).hom.app L) =
      d.completionUnit U ((d.pull h).obj L) := by
    dsimp only [AdicCoefficientDatum.ordinaryToCompleted, AdicCoefficientDatum.completionUnit]
    rw [Category.assoc, ← Functor.map_comp, Category.assoc, ha]
    simp only [Iso.inv_hom_id_app_assoc]
  have hp := (d.towerProjection_properties p ((d.pull h).obj L)).2.2
  refine ⟨hu, hp, ?_⟩
  have hi : d.completionUnit U ((d.pull h).obj L) ≫
      (completedRlim U (d.completedRing U)).map
        ((d.reductionTowerPullbackIso h).inv.app L) =
      d.ordinaryToCompleted h L := by
    rw [← hu, Category.assoc, ← Functor.map_comp]
    simp only [Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Functor.map_comp, ← Category.assoc, hp, Category.assoc]
  have hn := (d.directImageRlimIso p).hom.naturality
    ((d.reductionTowerPullbackIso h).inv.app L)
  change (d.push p).map ((completedRlim U (d.completedRing U)).map
      ((d.reductionTowerPullbackIso h).inv.app L)) ≫ _ =
    (d.directImageRlimIso p).hom.app _ ≫
      (completedRlim W (d.completedRing W)).map
        ((d.towerPush p).map ((d.reductionTowerPullbackIso h).inv.app L)) at hn
  erw [← hn, ← Category.assoc, ← Functor.map_comp, hi]
  rfl

/-- At (p,h,L) = (f',g',K) the target projection is precisely H prime of strict
exchange normalization. The last factor in completed base change is precisely the
inverse of c_Q at the same strict pulled reduction tower, with its specified orientation.

Source: Stacks Project, Tag 0A07 and Equation 0B56; target identification in the
integral-lattice refinement of blueprint thm-weil-pbc-finite-extension
(blueprint: lem-weil-pbc-completed-target-augmentation-normalization).

Proof:
6. Substitute (f',g',K) in the general construction. By
   lem-weil-pbc-strict-tower-exchange-mate-normalization its target D is tower direct
   image of tower pullback of the reduction tower. Its H prime is the counit-tensor
   projection followed by direct image of t inverse, giving the first equation.
   def-weil-pbc-completed-base-change-map defines its final comparison to be the
   inverse of directImageRlimIso at exactly this pulled tower. Unfold its ordered
   composite to obtain the second equation. The witnesses are retained independently
   at every finite quotient; there is no extra compatibility or uniform bound. -/
theorem completedTargetAugmentationNormalization_square (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    (d.towerProjection f' ((d.pull g').obj K) ≫
        (d.towerPush f').map ((d.reductionTowerPullbackIso g').inv.app K) =
      (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
    (d.completedBaseChangeMap sq K hK W =
      (completedRlim Y' (d.completedRing Y')).map
          (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫
        (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
          (d.directImageRlimIso f').inv.app
            ((d.towerPull g').obj ((completedReductionTower X d).obj K))) := by
  constructor
  · rfl
  · rfl

end AlgebraicGeometry.Scheme
