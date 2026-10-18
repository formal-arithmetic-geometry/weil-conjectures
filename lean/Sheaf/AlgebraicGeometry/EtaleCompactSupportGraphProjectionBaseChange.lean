/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphProjection
import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafBaseChange

/-!
# Base change of termwise graph projections

Source: Stacks Project Tags 03S6, 0F4L, 07A7, 0E46 and 0E47.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] upperStar lowerStar etaleLowerShriek openImmersionLowerShriek

private theorem exact_square_normalization
    (A : Type (u + 1)) [CommRing A]
    {Z' Z X' X : Scheme.{u}} {t : Z' ⟶ Z} {p' : Z' ⟶ X'}
    {p : Z ⟶ X} {g : X' ⟶ X} (sq : CommSq t p' p g)
    (Y : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) p').leftDerivedFunctor.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app Y) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app Y ≫
      (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app Y) =
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p').hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj Y) ≫
      (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso (ModuleCat.{u + 1} A) sq)).hom.app Y ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) t).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj Y) := by
  simp only [derivedSquareUpperStarIso, squareUpperStarIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  let ep := (upperStar (ModuleCat.{u + 1} A) p').leftDerivedFunctorIsoMapDerivedCategory
  let et := (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctorIsoMapDerivedCategory
  have n₁ := ep.hom.naturality
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctorIsoMapDerivedCategory.inv.app Y)
  have n₂ := et.inv.naturality
    ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctorIsoMapDerivedCategory.hom.app Y)
  dsimp only [ep, et] at n₁ n₂
  rw [reassoc_of% n₁, ← n₂, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option maxHeartbeats 800000 in
-- Normalizing these comparison maps involves several dependent scheme categories.
/-- The termwise graph projections commute with the sum and open-extension exchanges.
Only exact functors on complexes occur in this equation; there is no total derived
proper direct image in either projection.
Source: Stacks Project Tags 03S6, 0F4L, 07A7, 0E46 and 0E47.
(blueprint: lem-a2-compact-support-graph-projection-base-change).

Proof: pull the clopen graph decomposition to the cartesian square. On the graph component,
both composites keep the same section of the corresponding etale lift; on the complement,
both are zero. The disjoint-cover sheaf axiom therefore gives equality of the sheaf
projections. The sum and open-extension exchanges are the left-adjoint comparisons of
the restriction/direct-image square; mate pasting identifies the two composition
comparisons. Apply this sheaf identity degreewise and descend through the homotopy
localization. The displayed exact-functor comparison maps insert the canonical
identifications of left-derived inverse image with termwise inverse image. The argument
uses no finiteness, nonempty-fibre, Noetherian or boundedness hypothesis. -/
theorem compactSupportGraphDerivedProjection_baseChange
    (A : Type (u + 1)) [CommRing A]
    {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (g : X' ⟶ X)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let c' := c.ofIsPullback (IsPullback.of_hasPullback g f).flip
    let h := pullback.snd g f
    let t := pullback.fst c.g g
    let E := (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory
    let E' := (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f)
      inferInstance).mapDerivedCategory
    let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c'.i).mapDerivedCategory
    let H := (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    let P' := (upperStar (ModuleCat.{u + 1} A) c'.g).leftDerivedFunctor
    P'.map ((exactEtaleSumExchange A f g).hom.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c'.g).hom.app
          (E'.obj (H.obj K)) ≫
        (compactSupportGraphDerivedProjection A (pullback.fst g f) c'
          (etaleCompactificationGraphMap A (pullback.fst g f) c')).app (H.obj K) =
      P'.map ((leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) g).inv.app (E.obj K)) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g g).toCommSq).hom.app (E.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) c.g).hom.app (E.obj K) ≫
            (compactSupportGraphDerivedProjection A f c
              (etaleCompactificationGraphMap A f c)).app K) ≫
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback g f).flip)).inv.app K ≫
        J'.map ((leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) h).hom.app K) := by
  let c' := c.ofIsPullback (IsPullback.of_hasPullback g f).flip
  let h := pullback.snd g f
  let t := pullback.fst c.g g
  let E := etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance
  let E' := etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f) inferInstance
  let P := upperStar (ModuleCat.{u + 1} A) c.g
  let P' := upperStar (ModuleCat.{u + 1} A) c'.g
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let J' := openImmersionLowerShriek (ModuleCat.{u + 1} A) c'.i
  let H := upperStar (ModuleCat.{u + 1} A) h
  let G := upperStar (ModuleCat.{u + 1} A) g
  let T := upperStar (ModuleCat.{u + 1} A) t
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback g f).flip
  let := isIso_etaleLowerShriekBaseChangeMap A g f
  let := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq
  have hd := Functor.mapDerivedCategoryNatTrans_projectionSquare E P J H E' P' J' G T
    (asIso (etaleLowerShriekBaseChangeMap A g f)).symm
    (squareUpperStarIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g g).toCommSq)
    (asIso (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq))
    (compactSupportGraphSheafProjection A f c (etaleCompactificationGraphMap A f c))
    (compactSupportGraphSheafProjection A (pullback.fst g f) c'
      (etaleCompactificationGraphMap A (pullback.fst g f) c'))
    (compactSupportGraphSheafProjection_baseChange A f c g) K
  have hx : P'.mapDerivedCategory.map ((exactEtaleSumExchange A f g).hom.app K) ≫
      (compactSupportGraphDerivedProjection A (pullback.fst g f) c'
        (etaleCompactificationGraphMap A (pullback.fst g f) c')).app
          (H.mapDerivedCategory.obj K) =
    (Functor.mapDerivedCategorySquareIso
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g g).toCommSq)).hom.app (E.mapDerivedCategory.obj K) ≫
      T.mapDerivedCategory.map ((compactSupportGraphDerivedProjection A f c
        (etaleCompactificationGraphMap A f c)).app K) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv.app K := by
    rw [← cancel_mono ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq).hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj]
    simpa only [compactSupportGraphDerivedProjection_termwise, NatTrans.comp_app,
      Functor.mapDerivedCategorySquareIso, exactEtaleSumExchange,
      mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.comp_obj, Category.comp_id,
      E, P, J, E', P', J', H, G, T, h, t, c', Compactification.ofIsPullback] using hd
  have np := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) c'.g).hom.naturality ((exactEtaleSumExchange A f g).hom.app K)
  have nt := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) t).hom.naturality
      ((compactSupportGraphDerivedProjection A f c (etaleCompactificationGraphMap A f c)).app K)
  have hn := exact_square_normalization A (IsPullback.of_hasPullback c.g g).toCommSq
    (E.mapDerivedCategory.obj K)
  dsimp only [E, P, J, E', P', J', H, G, T, h, t, c',
    Compactification.ofIsPullback] at hx np nt hn ⊢
  simp only [derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% np, hx]
  rw [reassoc_of% nt, reassoc_of% hn]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

end AlgebraicGeometry.Etale
