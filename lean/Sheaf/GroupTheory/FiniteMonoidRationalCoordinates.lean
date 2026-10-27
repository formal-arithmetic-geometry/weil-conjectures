/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Rational coordinates and the cone of finite monoid generators

Source: the agent-extracted finite-coordinate argument in parent
`lem-trf-sharp-cone-lattice-intersection`, steps 3--4; ILO, Exposé VIII,
Remark 3.1.29, printed p. 103, supplies the combinatorial fan motivation
(blueprint: lem-trf-finite-monoid-rational-coordinates).

We use `ℚ ⊗[ℤ] G`, canonically identified with `G ⊗[ℤ] ℚ` by
`TensorProduct.comm ℤ G ℚ`. Thus `q ⊗ₜ g` renders the node's `g ⊗ q`,
and the usual left-factor scalar action renders extension of scalars.
The sets `P` and `C` are specified by their defining finite-sum formulas.
-/

@[expose] public section

universe u

open scoped TensorProduct BigOperators

namespace TensorProduct

/-- A finite integral basis gives unique rational linear coordinates, the cone of natural
combinations of a finite group-generating family is its nonnegative rational cone, and
any integer expression of the basis in that family gives the displayed signed formula.
Source: parent `lem-trf-sharp-cone-lattice-intersection`, steps 3--4; ILO VIII,
Remark 3.1.29, printed p. 103 (motivation only)
(blueprint: lem-trf-finite-monoid-rational-coordinates).

Proof, following the six steps of the node:
1. Uniqueness of integral basis coordinates makes each coordinate additive and
   integer-linear, with its value on a basis vector the Kronecker delta. The tensor
   universal property (`def-weil-pbc-module-tensor-product`, Stacks 00CX) extends
   `(q,g) ↦ q * e.repr g k` to an integer-linear map on the tensor product.
2. For each rational scalar, the two integer-linear maps asserting rational linearity
   agree on pure tensors by the extension-of-scalars action
   (`def-weil-module-base-change`). Pure tensors generate, so they agree everywhere.
   The same generation proves uniqueness of the coordinate map.
3. The endomorphism `x ↦ ∑ k, L k x • (1 ⊗ₜ e k)` is the identity on pure tensors,
   by integral reconstruction and bilinearity, hence on every tensor by Stacks 00CX.
   Applying each `L k` to any other expansion recovers exactly its coefficient.
4. For each expression defining `C`, write every monoid element as a natural
   combination of the `p j`, distribute, and interchange the finite sums. The resulting
   coefficient of `p j` is a sum of products of nonnegative rationals with naturals.
   Conversely every `p j` belongs to `P`, so each nonnegative rational combination
   is an expression defining `C`. The empty sum supplies zero.
5. Apply `g ↦ 1 ⊗ₜ g` to each row of the given integer matrix, substitute into
   reconstruction, and interchange sums to get coefficients `∑ k, L k x * b k j`.
   For every rational `c`, splitting into `c ≥ 0` and `c ≤ 0` proves
   `c = max c 0 - max (-c) 0`. Distribute this identity through the sum.
   The group-generation hypothesis supplies such rows whenever needed.
6. Empty index types are allowed throughout. If the basis is empty, integral
   reconstruction gives `G = 0`, and pure-tensor generation gives the zero tensor space.
   If the generator family is empty, group-generation gives the same conclusion.
   In either case all applicable sums vanish; when the basis is empty but generators
   remain, every generator and every signed coefficient is zero. -/
theorem finite_monoid_rational_coordinates
    (G : Type u) [AddCommGroup G] (r m : ℕ) (e : Module.Basis (Fin r) ℤ G)
    (p : Fin m → G)
    (hp : ∀ g : G, ∃ a : Fin m → ℤ, g = ∑ j, a j • p j)
    (P : Set G) (hP : P = {g | ∃ a : Fin m → ℕ, g = ∑ j, a j • p j})
    (C : Set (TensorProduct ℤ ℚ G))
    (hC : C = {x | ∃ (n : ℕ) (v : Fin n → G) (q : Fin n → ℚ),
      (∀ l, v l ∈ P) ∧ (∀ l, 0 ≤ q l) ∧ x = ∑ l, q l ⊗ₜ[ℤ] v l}) :
    ∃ L : Fin r → (TensorProduct ℤ ℚ G →ₗ[ℚ] ℚ),
      (∀ (k : Fin r) (g : G) (q : ℚ), L k (q ⊗ₜ[ℤ] g) = q * (e.repr g k : ℚ)) ∧
      (∀ (k : Fin r) (L' : TensorProduct ℤ ℚ G →ₗ[ℚ] ℚ),
        (∀ (g : G) (q : ℚ), L' (q ⊗ₜ[ℤ] g) = q * (e.repr g k : ℚ)) → L' = L k) ∧
      (∀ x : TensorProduct ℤ ℚ G, x = ∑ k, L k x • ((1 : ℚ) ⊗ₜ[ℤ] e k)) ∧
      (∀ (x : TensorProduct ℤ ℚ G) (d : Fin r → ℚ),
        x = ∑ k, d k • ((1 : ℚ) ⊗ₜ[ℤ] e k) → ∀ k, d k = L k x) ∧
      C = {x | ∃ q : Fin m → ℚ, (∀ j, 0 ≤ q j) ∧ x = ∑ j, q j ⊗ₜ[ℤ] p j} ∧
      (∀ b : Fin r → Fin m → ℤ, (∀ k, e k = ∑ j, b k j • p j) →
        ∀ x : TensorProduct ℤ ℚ G,
          x = (∑ j, max (∑ k, L k x * (b k j : ℚ)) 0 ⊗ₜ[ℤ] p j) -
            ∑ j, max (-(∑ k, L k x * (b k j : ℚ))) 0 ⊗ₜ[ℤ] p j) ∧
      (m = 0 → (∀ g : G, g = 0) ∧ (∀ x : TensorProduct ℤ ℚ G, x = 0)) := by
  sorry

end TensorProduct
