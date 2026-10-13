/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ArrowProductTransitionsExistence
import WeilConjectures.CategoryTheory.ArrowProductTransitionsCocycleLaw

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0EXZ, the arrow-indexed product construction.
(blueprint: lem-weil-pbc-arrow-product-transitions-cocycle)

Proof in words: each continuous pushforward R_a is a right adjoint, so preserves
products. Define q_a by the universal property of the product preserved by R_a:
its t-component is the projection indexed by a ≫ t followed by the inverse
composition comparison at A_t. For composable a,b, test the cocycle after each
mapped projection indexed by t. Naturality of the composition comparison moves
that projection through the comparison. The two sides then project to the
factors indexed by (a ≫ b) ≫ t and a ≫ (b ≫ t), identified by associativity.
The remaining comparison maps agree by associativity of precomposition: their
underlying presheaf components are transports along the same equality of
functors F(a ≫ b ≫ t). Thus the mapped product universal property gives the
cocycle. Empty products pose no problem, since the same universal property
has an empty family of equations. No data from Fs, φ, or ι are needed. -/
theorem exists_arrow_product_transitions_cocycle
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (T : ∀ j : J, GrothendieckTopology (F.obj j))
    [∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor.IsContinuous (T j) (T k)]
    (A : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u}) :
    let R := fun {j k : J} (a : j ⟶ k) ↦
      (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
    let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
    ∃ (q : ∀ {j k : J} (a : j ⟶ k), B j ⟶ (R a).obj (B k)),
      (∀ {j k : J} (a : j ⟶ k) (t : Σ l : J, k ⟶ l),
        q a ≫ (R a).map (Pi.π _ t) =
          Pi.π _ ⟨t.1, a ≫ t.2⟩ ≫
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a t.2).symm))
              AddCommGrpCat.{u} (T j) (T k) (T t.1)).inv.app (A t.1)) ∧
      (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        q (a ≫ b) = q a ≫ (R a).map (q b) ≫
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
            AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (B l)) := by
  dsimp
  obtain ⟨q, hq⟩ := exists_arrow_product_transitions F T A
  refine ⟨q, hq, ?_⟩
  exact arrow_product_transitions_cocycle_of_projections F T A q hq
end CategoryTheory
