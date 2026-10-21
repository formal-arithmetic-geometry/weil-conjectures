/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Tensor action of the unit-defined left-adjoint projection

Source: Stacks Project, Cohomology on Sites, Tag 0GL1, and Modules on Sites, Tag 0E8I,
`lemma-j-shriek-and-tensor`; the abstract coherence calculation is agent-written
(blueprint: lem-pur-unit-adjunct-tensor-action).

The map used below is the existing `Adjunction.projectionMap`, with the forward tensorator
of the strong monoidal right adjoint. Its defining transpose is the unit tensored with
an identity, followed by that tensorator. Thus no second projection map is defined here.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open MonoidalCategory

/-- The unit-defined projection of a left adjoint to a strong monoidal functor is natural,
associative as a tensor action, and compatible with the adjunction counit.

Source: the agent-written abstract calculation underlying Stacks Tags 0GL1 and 0E8I,
`lemma-j-shriek-and-tensor` (blueprint: lem-pur-unit-adjunct-tensor-action).

Write `m` for the forward tensorator of `Q`, and `k` for the displayed components of
`projectionMap`. The node's inverse comparison `mu` is the inverse of `m`.
The existing `projectionMap_app_app` and `unit_app_comp_map_projectionMap_app_app`
identify `k` with the unique inverse Hom transpose of `(v_M tensor 1) followed by m`.
No invertibility of `k`, full faithfulness, symmetry, closedness or exactness is assumed.

Proof (the node's seven steps):
1. By the natural Hom bijection of lem-weil-pbc-adjunction-of-natural-bijection,
   the transpose of `k` is `(v_M tensor 1) followed by m`.
2. Transpose joint naturality. Tensorator naturality from def-sfb-strong-monoidal-functor
   and unit naturality identify the two transposes; the Hom bijection is injective.
3. Transpose the iterated action on the left. Naturality and step 1 give
   `((v_M tensor 1) tensor 1)`, then `(m tensor 1)`, then `m`.
4. Transpose the right side, retaining the inverse associator in the target. Associator
   naturality and tensor bifunctoriality from def-sfb-monoidal-category rewrite its
   initial factors as `((v_M tensor 1) tensor 1)`, then the source associator,
   then `(1 tensor m)`, then `m`, then `Q` of the inverse target associator.
5. Tensorator associativity from def-sfb-strong-monoidal-functor equates steps 3 and 4
   after cancelling the image of the target associator against its inverse.
   Injectivity of the Hom bijection proves the action equation.
6. Transpose `J(m) followed by e`. Naturality gives `m`, then `v`, then `Q(e)`;
   the right triangle identity reduces this to `m`.
7. Transpose `k followed by (e tensor 1)`. Step 1 and tensorator naturality give
   `(v tensor 1)`, then `(Q(e) tensor 1)`, then `m`. The same triangle identity
   reduces this to `m`. Injectivity proves the counit equation. -/
theorem unitAdjunctTensorAction
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    {J : C ⥤ D} {Q : D ⥤ C} (adj : J ⊣ Q) [Q.Monoidal] :
    (∀ {M M' : C} {N N' : D} (a : M ⟶ M') (h : N ⟶ N'),
      J.map (a ⊗ₘ Q.map h) ≫
          ((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
            (Functor.LaxMonoidal.μNatTrans Q)).app M').app N' =
        ((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
          (Functor.LaxMonoidal.μNatTrans Q)).app M).app N ≫ (J.map a ⊗ₘ h)) ∧
    (∀ (M : C) (N₁ N₂ : D),
      ((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
          (Functor.LaxMonoidal.μNatTrans Q)).app (M ⊗ Q.obj N₁)).app N₂ ≫
          (((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
            (Functor.LaxMonoidal.μNatTrans Q)).app M).app N₁ ⊗ₘ 𝟙 N₂) =
        J.map ((α_ M (Q.obj N₁) (Q.obj N₂)).hom ≫
          (𝟙 M ⊗ₘ Functor.LaxMonoidal.μ Q N₁ N₂)) ≫
          ((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
            (Functor.LaxMonoidal.μNatTrans Q)).app M).app (N₁ ⊗ N₂) ≫
          (α_ (J.obj M) N₁ N₂).inv) ∧
    (∀ (F N : D),
      J.map (Functor.LaxMonoidal.μ Q F N) ≫ adj.counit.app (F ⊗ N) =
        ((adj.projectionMap Q (curriedTensor C) (curriedTensor D)
          (Functor.LaxMonoidal.μNatTrans Q)).app (Q.obj F)).app N ≫
          (adj.counit.app F ⊗ₘ 𝟙 N)) := by
  sorry

end CategoryTheory.Adjunction
