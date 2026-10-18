/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.AffineInfiniteProductExistence
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Surjectivity of products of affine morphisms

Source: Stacks Project, Limits, Tag 0CNJ, lemma-infinite-product-surjective
(blueprint: lem-trf-infinite-product-surjective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `S` be a scheme and let `g j : T j ⟶ S` be a small family of affine,
surjective morphisms.  The product cone supplied by
`exists_affine_infinite_product` has a surjective structure morphism to `S`.

Source: Stacks Project, Limits, Tag 0CNJ, lemma-infinite-product-surjective
(blueprint: lem-trf-infinite-product-surjective).

Proof: For a point of `S`, choose a point above it in each `T j`.  The induced
residue-field extensions embed compatibly in a common field.  The corresponding
maps from its spectrum to the `T j` are over the same map to `S`; the universal
property of the affine product cone therefore gives a map to its vertex.  The
image of the unique point of that spectrum lies above the chosen point.  The
empty family is handled by the same universal property of the terminal object
of schemes over `S`.
-/
theorem infinite_product_surjective
    (S : Scheme.{u}) (J : Type u) (T : J → Scheme.{u})
    (g : ∀ j : J, T j ⟶ S)
    (h_affine : ∀ j : J, IsAffineHom (g j))
    (h_surjective : ∀ j : J, Surjective (g j)) :
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
                hY j)) ∧
        Surjective c.pt.hom := by
  sorry

end AlgebraicGeometry
