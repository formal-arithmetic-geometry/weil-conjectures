/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensoring finitely presented modules with arbitrary products

Source: Stacks Project, Algebra, Tag 059K, implication (1) implies (2)
(blueprint: lem-trf-finite-presentation-tensor-products).
-/

@[expose] public section

universe u v w t

namespace TensorProduct

/-- Tensoring a finitely presented module with an arbitrary product commutes with that product.
The comparison is the canonical linear map sending `p ⊗ₜ q` to `fun a ↦ p ⊗ₜ q a`.
The product is the dependent function module with componentwise operations. No finiteness or
flatness is required of the factors, and the index type may be empty or infinite.

Source: Stacks Project, Algebra, Tag 059K, implication (1) implies (2).
(blueprint: lem-trf-finite-presentation-tensor-products)

Proof:
1. By def-sc-finitely-presented-module, choose a finite presentation
   R^m -> R^n -> P -> 0 (Module.FinitePresentation.exists_fin'). Use this same
   presentation for the whole family, allowing m = 0, n = 0 and an empty index type.
2. Tensor it with the product of the Q a, and separately with each Q a.
   By lem-weil-pbc-tensor-right-exact the rows are right exact. Their coordinatewise
   product is right exact as well: exactness and surjectivity are checked coordinatewise,
   choosing a lift in each coordinate. For a finite free module R^r, its comparison is
   an isomorphism since both sides identify with the r-fold power of the product.
   The resulting diagram commutes on pure tensors by def-weil-pbc-module-tensor-product.
3. For surjectivity, lift a family in the bottom right to the product of R^n tensor Q a,
   lift across the middle finite-free comparison, and map along the top row.
   Commutativity gives a preimage under the desired comparison.
4. For injectivity, lift an element of the kernel to b in R^n tensor the product.
   Its middle comparison image is in the kernel of the bottom row. Exactness gives a
   preimage in the product of R^m tensor Q a. Lift that across the left comparison.
   Commutativity and injectivity of the middle comparison show its top-row image is b.
   Top-row exactness then shows the original element is zero. -/
theorem piRightHom_bijective_of_finitePresentation
    (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] (A : Type w) (Q : A → Type t)
    [∀ a : A, AddCommGroup (Q a)] [∀ a : A, Module R (Q a)] :
    Function.Bijective (TensorProduct.piRightHom R R P Q) := by
  sorry

end TensorProduct
