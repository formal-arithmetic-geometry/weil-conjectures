/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Sheaf.RingTheory.FinitePresentationTensorProducts

/-!
# A product tensor kernel controlled by a finitely presented factorization

Source: Stacks Project, Algebra, Tag 059M, proof of (1) implies (2), the three-row
comparison diagram (blueprint: lem-trf-fp-factorization-product-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y t

open scoped TensorProduct

namespace LinearMap

/-- Suppose `b = c.comp a`, the target `Q` of `a` is finitely presented, and every tensor
kernel of `b` is contained in the corresponding tensor kernel of `a`. If the product
comparison kills `b` tensored with a product, then both `a` and `b` tensored with that
product kill the original element. Products have their componentwise module structures.
The index type may be empty or infinite; neither `P` nor `T` is assumed finite or flat.
The test-module universe is an arbitrary common upper universe for the given modules.

Source: Stacks Project, Algebra, Tag 059M, proof of (1) implies (2), three-row diagram.
(blueprint: lem-trf-fp-factorization-product-kernel)

Proof:
1. For each index i, project z to z_i in P tensor L_i. Naturality of tensor maps
   (def-weil-pbc-module-tensor-product), checked on pure tensors, identifies the i-th
   coordinate of the given zero comparison image with (b tensor id)(z_i). Thus it is zero.
2. Apply the assumed kernel inclusion to L_i. It gives (a tensor id)(z_i) = 0.
   Naturality again identifies these elements with the coordinates of the comparison
   image of (a tensor id)(z), so that comparison image is zero.
3. Since Q is finitely presented (def-sc-finitely-presented-module), its comparison is
   bijective by lem-trf-finite-presentation-tensor-products. Injectivity gives the first
   conclusion (a tensor id)(z) = 0. This also applies to the empty product.
4. The equation b = c.comp a and functoriality of tensor maps give
   (b tensor id)(z) = (c tensor id)((a tensor id)(z)) = 0, the second conclusion. -/
theorem rTensor_eq_zero_of_fp_factorization_product_kernel
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (Q : Type w) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (T : Type x) [AddCommGroup T] [Module R T]
    (a : P →ₗ[R] Q) (b : P →ₗ[R] T) (c : Q →ₗ[R] T) (hfactor : b = c.comp a)
    (hker : ∀ (L : Type (max u v w x t)) [AddCommGroup L] [Module R L],
      LinearMap.ker (b.rTensor L) ≤ LinearMap.ker (a.rTensor L))
    (A : Type y) (L : A → Type (max u v w x t))
    [∀ i : A, AddCommGroup (L i)] [∀ i : A, Module R (L i)]
    (z : P ⊗[R] (∀ i : A, L i))
    (hz : TensorProduct.piRightHom R R T L (b.rTensor (∀ i : A, L i) z) = 0) :
    a.rTensor (∀ i : A, L i) z = 0 ∧ b.rTensor (∀ i : A, L i) z = 0 := by
  sorry

end LinearMap
