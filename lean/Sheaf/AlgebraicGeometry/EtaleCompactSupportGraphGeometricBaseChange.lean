/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphProjectionBaseChange

/-!
# The graph comparison under geometric base change

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 07A7
(blueprint: lem-asd-compact-support-graph-geometric-base-change).
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar etaleLowerShriek openImmersionLowerShriek

private theorem graph_baseChange_of_projections
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')
    (G₀ G : C ⥤ C') (T : D ⥤ D') (μ : G₀ ⟶ G)
    (θ : G ⋙ L' ⟶ L ⋙ T)
    {E : C} {E' : C'} {J : D} {J' : D'}
    (a : E ⟶ R.obj J) (a' : E' ⟶ R'.obj J')
    (δ : L.obj E ⟶ J) (δ' : L'.obj E' ⟶ J')
    (σ : G₀.obj E ⟶ E') (j : T.obj J ⟶ J')
    (ha : L.map a ≫ adj.counit.app J = δ)
    (ha' : L'.map a' ≫ adj'.counit.app J' = δ')
    (hδ : L'.map σ ≫ δ' = L'.map (μ.app E) ≫ θ.app E ≫ T.map δ ≫ j) :
    G₀.map a ≫ μ.app (R.obj J) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ)).natTrans.app J ≫ R'.map j =
      σ ≫ a' := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have nj := adj'.counit.naturality j
  dsimp only [Functor.comp_map, Functor.id_map] at nj
  rw [nj, reassoc_of% (mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ θ) J)]
  have nμ := μ.naturality a
  have nθ := θ.naturality a
  dsimp only [Functor.comp_map] at nθ
  rw [← L'.map_comp_assoc, nμ, L'.map_comp_assoc, reassoc_of% nθ,
    ← T.map_comp_assoc, ha, ha']
  exact hδ.symm

/-- The forward graph map commutes with the specified compact-support exchange at a
geometric point over an arbitrary scheme. This is equality of unbounded derived
transformations; neither scheme needs to be Noetherian or quasi-compact.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6, 07A7, 0E46 and 0E47.
(blueprint: lem-asd-compact-support-graph-geometric-base-change).

Proof:
Pull the compactification graph to the geometric point. The inverse sum exchange and
its graph composition comparison preserve their defining adjunctions. Transpose the two
sheaf projections: on the pulled-back clopen graph both restrict to identity, and on the
complement both restrict to zero. The disjoint-cover sheaf axiom equates the projections;
mate pasting identifies the intervening inverse-image square comparisons. Apply these
sheaf transformations degreewise. Localization full faithfulness descends their equality
to arbitrary unbounded complexes, with the specified exact-functor comparators. Transpose
under the pulled-back proper direct-image adjunction. By the definition of proper exchange
and its counit law, the transpose of the left side is the pulled-back graph projection;
the transpose of the right side is the equal graph projection from the sheaf calculation.
Injectivity of the adjunction hom equivalence proves the equality. This uses equality
before testing stalks, and includes an empty geometric fibre and the zero ring. -/
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip))) := by
  let g := X.algClosurePoint y
  let c' := c.ofIsPullback (IsPullback.of_hasPullback g f).flip
  let h := pullback.snd g f
  let t := pullback.fst c.g g
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c'.i).mapDerivedCategory
  ext K
  have hh := graph_baseChange_of_projections
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c'.g)
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g g).toCommSq).hom
    ((compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c)).app K)
    ((compactSupportDerivedComparison A (pullback.fst g f) c'
      (etaleCompactificationGraphMap A (pullback.fst g f) c')).app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K))
    _ _ ((exactEtaleSumExchange A f g).hom.app K)
    ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
        (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback g f).flip)).inv.app K ≫
      J'.map ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) h).hom.app K))
    (compactSupportDerivedComparison_leftDerived_transpose A f c _ K)
    (compactSupportDerivedComparison_leftDerived_transpose A (pullback.fst g f) c' _ _)
    (compactSupportGraphDerivedProjection_baseChange A f c g K)
  dsimp only [c', Compactification.ofIsPullback] at hh
  simpa only [exactCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.id_obj, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc,
    derivedBaseChangeMap, derivedBaseChangeSquare, J, J', g, h, t, c',
    Compactification.ofIsPullback_g, Compactification.ofIsPullback,
    rightDerivedLowerShriekOfCompactification] using hh

end AlgebraicGeometry.Etale
