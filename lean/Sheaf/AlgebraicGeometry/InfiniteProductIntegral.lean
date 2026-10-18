/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.AffineInfiniteProductExistence
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Products of integral morphisms are integral

Source: Stacks Project, Limits, Tag 0CNK, `lemma-infinite-product-integral`
(blueprint: lem-trf-infinite-product-integral).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The structure morphism of a small product of integral schemes over `S` is integral.
The product is represented by a limiting fan in `Over S`; it exists by
`exists_affine_infinite_product`, since integral morphisms are affine. No nonemptiness
assumption is imposed on the index type.

Source: Stacks Project, Limits, Tag 0CNK, `lemma-infinite-product-integral`
(blueprint: lem-trf-infinite-product-integral).

Proof plan:
1. Integral morphisms are affine (`def-weil-finite-integral-morphism`). Apply
   `lem-trf-affine-infinite-product-existence`; its affine projection to the empty finite
   subproduct shows that the product structure morphism is affine. Over an affine open
   `U = Spec A` of `S`, write its inverse image as `Spec B` and the inverse images in the
   factors as `Spec B_j` (`pqf-def-affine-morphism`, `def-weil-affine-spectrum`). Each
   map `A → B_j` is integral.
2. Restriction to `U` preserves the product universal property: a map into the product
   whose composite to `S` factors through `U` factors uniquely through its inverse image
   (`def-weil-open-immersion`). Thus `Spec B` is the product of the `Spec B_j` over `U`.
3. Full faithfulness of `Spec` (`def-weil-affine-spectrum`) identifies this universal
   property with the coproduct universal property of `B` among commutative `A`-algebras.
4. Each coproduct map `B_j → B` sends a monic equation over `A` to a monic equation over
   `A`. Hence its image consists of integral elements (`def-weil-pbc-integral-closure`).
5. The integral closure `C` of `A` in `B` is an `A`-subalgebra containing all these images.
   Factor the coproduct maps through `C` and obtain an `A`-algebra map `r : B → C` by
   the coproduct universal property (`def-weil-pbc-integral-closure`).
6. The inclusion `e : C → B` satisfies `e ∘ r = id` by coproduct uniqueness, so every
   element of `B` is integral over `A`. This holds on every affine open of `S`, and the
   structure morphism is affine, so it is integral. For an empty index set the same
   argument uses the initial `A`-algebra property, or the terminal object `S` of `Over S`.
-/
theorem isIntegralHom_infinite_product
    (S : Scheme.{u}) (J : Type u) (T : J → Scheme.{u})
    (g : ∀ j : J, T j ⟶ S) (h_integral : ∀ j : J, IsIntegralHom (g j))
    (c : Fan (fun j : J ↦ Over.mk (g j))) (hc : IsLimit c) :
    IsIntegralHom c.pt.hom := by
  sorry

end AlgebraicGeometry
