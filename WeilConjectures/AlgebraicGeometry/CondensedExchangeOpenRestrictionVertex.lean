/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.exchange

/-- The geometric vertex used by the one-open comparison square.

Given a chosen Cartesian square and the three Cartesian presentations over an open
`v : U ⟶ Y`, the universal property of the chosen square supplies a map
`t : XU' ⟶ X'`. It is characterized by the two displayed projection equations:
`t ≫ g' = hU ≫ a` and `t ≫ f' = fU' ≫ b`. These equations are the precise
vertex data needed to instantiate `RingedRestrictionExchange.open_restriction`.

Source: Stacks Project, Tags 0D6F and 07A7, with the pullback vertex construction
used in the open-restriction proof.
(blueprint: lem-sfb-condensed-exchange-one-open-restriction-vertex).
Proof: lift the two composites `hU ≫ a` and `fU' ≫ b` into `pullback f g` and
compose with `sq.isoPullback.inv`. The equality required by the lifting property,
`hU ≫ a ≫ f = fU' ≫ b ≫ g`, follows by rewriting `wf.w`, `w.w` and `wg.w`
(both sides become `fU' ≫ gU ≫ v`); the two projection equations follow from
`sq.hom_fst`, `sq.hom_snd`, `pullback.lift_fst` and `pullback.lift_snd`.
No uniqueness or extra geometric
hypothesis is used, and the construction also applies when `U` is empty. -/
theorem condensed_exchange_one_open_restriction_vertex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (v : U ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ U)
    (b : YU' ⟶ Y') (gU : YU' ⟶ U)
    (hU : XU' ⟶ XU) (fU' : XU' ⟶ YU')
    (wf : IsPullback a fU f v) (wg : IsPullback b gU g v)
    (w : IsPullback hU fU' fU gU) :
    ∃ t : XU' ⟶ X', t ≫ g' = hU ≫ a ∧ t ≫ f' = fU' ≫ b := by
  refine ⟨pullback.lift (hU ≫ a) (fU' ≫ b) ?_ ≫ sq.isoPullback.inv, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, wf.w, wg.w, ← Category.assoc, w.w, Category.assoc]
  · have h : sq.isoPullback.inv ≫ g' = pullback.fst f g :=
      (Iso.inv_comp_eq _).2 sq.hom_fst.symm
    rw [Category.assoc, h, pullback.lift_fst]
  · have h : sq.isoPullback.inv ≫ f' = pullback.snd f g :=
      (Iso.inv_comp_eq _).2 sq.hom_snd.symm
    rw [Category.assoc, h, pullback.lift_snd]

end AlgebraicGeometry.ProEtale.CondensedRing
