/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Sheaf.AlgebraicGeometry.LimitAffineTransition

/-!
# Products of affine scheme morphisms exist

Source: Stacks Project, Limits, Tag 0CNI, `lemma-infinite-product`
(blueprint: lem-trf-affine-infinite-product-existence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `S` be a scheme and let `g j : T j ⟶ S` be a small family of affine morphisms.
The finite-subproduct diagram has a limiting cone whose vertex is the product of the
family in `Over S`; all projections to finite fibre products are affine. This is the
formal statement of Stacks Project, Limits, Tag 0CNI
(blueprint: lem-trf-affine-infinite-product-existence). The index type has the same universe
as the schemes, as required by the size convention. The proof constructs finite products by
induction, identifies the transition maps as affine base changes, applies
`exists_limit_affine_transition`, and checks the universal property of the resulting
cone; the empty family is handled by the terminal object `S` in `Over S`.
-/
theorem exists_affine_infinite_product
    (S : Scheme.{u}) (J : Type u) (T : J → Scheme.{u})
    (g : ∀ j : J, T j ⟶ S)
    (h_affine : ∀ j : J, IsAffineHom (g j)) :
    ∃ c : Cone
        (ProductsFromFiniteCofiltered.liftToFinsetObj
          (Discrete.functor (fun j : J => Over.mk (g j)))),
      Nonempty (IsLimit c) ∧
        (∀ F : (Finset (Discrete J))ᵒᵖ,
          IsAffineHom (c.π.app F).left) ∧
        (∀ (Y : Over S) (hY : ∀ j : J, Y ⟶ Over.mk (g j)),
          ∃! q : Y ⟶ c.pt,
            (∀ j : J,
              q ≫
                  (c.π.app (op ({Discrete.mk j} : Finset (Discrete J))) ≫
                    Pi.π
                      (fun x : ({Discrete.mk j} : Finset (Discrete J)) =>
                        Over.mk (g x.1.as))
                      ⟨Discrete.mk j, by simp⟩) =
                hY j)) := by
  sorry

end AlgebraicGeometry
