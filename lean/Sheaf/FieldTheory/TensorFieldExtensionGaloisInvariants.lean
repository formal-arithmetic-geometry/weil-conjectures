/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Invariants of a tensor product with a field extension

Source: Stacks Project, Varieties, proof of Lemma 038B (lemma-closed-fixed-by-Galois),
computation of the invariant polynomial coefficients
(blueprint: lem-weil-pbc-tensor-field-extension-galois-invariants).
-/

universe u v w

open scoped TensorProduct

namespace TensorProduct

/-- Extension by `a ↦ a ⊗ 1` embeds a vector space as the invariants of the action on
its second tensor factor, when the automorphism group's fixed field is the base field.
Source: Stacks Project, Varieties, proof of Lemma 038B
(blueprint: lem-weil-pbc-tensor-field-extension-galois-invariants).

Proof:
1. Choose a `k`-basis `(eᵢ)` of `A` using
   lem-weil-pbc-vector-space-basis-through-vector with the empty prescribed set.
2. Scalar extension (def-weil-vector-space-scalar-extension) gives the `M`-basis
   `(eᵢ ⊗ 1)`, so every tensor has unique finitely supported coordinates in `M`.
3. The universal property makes `id ⊗ τ` act coordinatewise: its coordinates are `τ(yᵢ)`.
4. Every `a ⊗ 1` is fixed since each algebra automorphism preserves one.
5. For a fixed tensor, uniqueness of coordinates gives `τ(yᵢ) = yᵢ` for every `τ`.
   The fixed-field hypothesis puts each coordinate in the image of `k`. Injectivity of
   `algebraMap k M` (def-pc-field-extension) preserves finite support. Bilinearity now
   writes the tensor as `(∑ᵢ cᵢ eᵢ) ⊗ 1`.
6. If `a ⊗ 1 = 0`, coordinate uniqueness and injectivity of `algebraMap k M` force
   every coordinate of `a` to vanish, proving injectivity. -/
theorem injective_and_range_eq_invariants
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    (G : Subgroup (M ≃ₐ[k] M))
    (hfixed : {y : M | ∀ τ : G, (τ : M ≃ₐ[k] M) y = y} =
      Set.range (algebraMap k M))
    (A : Type w) [AddCommGroup A] [Module k A] :
    Function.Injective ((TensorProduct.mk k A M).flip (1 : M)) ∧
      Set.range ((TensorProduct.mk k A M).flip (1 : M)) =
        {z : A ⊗[k] M | ∀ τ : G,
          LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap z = z} := by
  sorry

end TensorProduct

namespace Algebra.TensorProduct

/-- For a `k`-algebra, the same invariant set is the image subalgebra `A ⊗ 1`, canonically
isomorphic to `A` by `a ↦ a ⊗ 1`.
Source: Stacks Project, Varieties, proof of Lemma 038B
(blueprint: lem-weil-pbc-tensor-field-extension-galois-invariants).

Proof: apply the six-step basis argument of `TensorProduct.injective_and_range_eq_invariants`
to the underlying vector space of `A`. The map `includeLeft` is the algebra homomorphism
`a ↦ a ⊗ 1`, so its image is the invariant set and its injectivity gives an algebra
isomorphism onto its range. This is the parenthetical clause of the node. -/
theorem range_eq_invariants_and_equiv
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    (G : Subgroup (M ≃ₐ[k] M))
    (hfixed : {y : M | ∀ τ : G, (τ : M ≃ₐ[k] M) y = y} =
      Set.range (algebraMap k M))
    (A : Type w) [Ring A] [Algebra k A] :
    (↑(Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).range : Set (A ⊗[k] M)) =
        {z : A ⊗[k] M | ∀ τ : G,
          LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap z = z} ∧
      ∃ e : A ≃ₐ[k] (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).range,
        ∀ a : A, (e a : A ⊗[k] M) = a ⊗ₜ[k] (1 : M) := by
  sorry

end Algebra.TensorProduct
