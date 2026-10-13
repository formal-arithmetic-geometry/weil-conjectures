/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

Proof: Mathlib's `IsIdempotentElem.isProj_range` and `IsProj.eq_conj_prodMap`
identify `p` with the conjugate of the identity on its range and zero on its kernel.
Thus `kⁿ = range p ⊕ ker p`, with `p` the identity and zero on the two summands.
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
  classical
  have hdim := p.finrank_range_add_finrank_ker
  have hn : Module.finrank k (Fin n → k) = n := by simp
  rw [hn] at hdim
  have hker : Module.finrank k p.ker = n - Module.finrank k p.range := by omega
  have hchar : (LinearMap.toMatrix b b p).charpoly =
      (Polynomial.X - 1) ^ Module.finrank k p.range *
        Polynomial.X ^ (n - Module.finrank k p.range) := by
    rw [charpoly_toMatrix]
    conv_lhs => rw [(IsIdempotentElem.isProj_range p hp).eq_conj_prodMap]
    rw [LinearEquiv.charpoly_conj, charpoly_prodMap]
    change (1 : Module.End k p.range).charpoly * (0 : Module.End k p.ker).charpoly = _
    rw [charpoly_one, charpoly_zero, hker]
  refine ⟨hchar, ?_⟩
  rw [hchar, mul_comm ((Polynomial.X - 1) ^ Module.finrank k p.range)]
  exact mul_dvd_mul (pow_dvd_pow _ (Nat.sub_le _ _))
    (pow_dvd_pow _ (by omega))

end LinearMap
