/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Sheaf.LinearAlgebra.IdempotentImageBaseChange

/-!
# Characteristic polynomial of an idempotent endomorphism over a field

Source: Stacks Project, More on Algebra, proof of Lemma 07M5
(blueprint: lem-weil-pbc-idempotent-endomorphism-charpoly-field).
-/

@[expose] public section

universe u

namespace LinearMap

/-- The characteristic polynomial of an idempotent on `kⁿ`, in any basis, and its divisibility.
Source: Stacks Project, More on Algebra, proof of Lemma 07M5
(blueprint: lem-weil-pbc-idempotent-endomorphism-charpoly-field).

The hypothesis `p ∘ p = p` is `IsIdempotentElem p` in `Module.End k (Fin n → k)`, whose
multiplication is composition.

Proof: The image decomposition of
[lem-weil-pbc-idempotent-endomorphism-image-base-change], specialized to `k`, gives
`kⁿ = range p ⊕ ker p`. Idempotence makes `p` the identity on its image and zero on its kernel.
Both subspaces are finite dimensional. Rank-nullity
[lem-weil-pbc-idempotent-charpoly-rank-nullity] gives kernel dimension `n - r`, where
`r = dimₖ(range p)`. Concatenate bases of the image and kernel. Basis invariance
[lem-weil-pbc-charpoly-free-module-properties] and the direct-sum formula
[lem-weil-pbc-charpoly-direct-sum-free] express the characteristic polynomial as the product
of those of the identity and zero on the two summands. Apply
[lem-weil-pbc-idempotent-charpoly-identity] and [lem-weil-pbc-idempotent-charpoly-zero] to get
`(X - 1)^r * X^(n - r)`. Finally `r ≤ n` and `n - r ≤ n`, so each factor divides its
corresponding `n`-th power; their product divides `X^n * (X - 1)^n`. -/
theorem charpoly_toMatrix_of_idempotent {k : Type u} [Field k] (n : ℕ)
    (p : Module.End k (Fin n → k)) (hp : IsIdempotentElem p)
    (b : Module.Basis (Fin n) k (Fin n → k)) :
    let r := Module.finrank k (LinearMap.range p)
    (LinearMap.toMatrix b b p).charpoly = (Polynomial.X - 1) ^ r * Polynomial.X ^ (n - r) ∧
      (LinearMap.toMatrix b b p).charpoly ∣
        (Polynomial.X : Polynomial k) ^ n * (Polynomial.X - 1) ^ n := by
  sorry

end LinearMap
