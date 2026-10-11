/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Images of finite free projectors under base change

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, final projector argument
(blueprint: lem-weil-pbc-idempotent-endomorphism-image-base-change).
-/

universe u v

open TensorProduct

namespace LinearMap

/-- The image of a finite free projector is finite projective and commutes with base change.
Source: Stacks Project, More on Algebra, proof of Lemma Tag 07M5, final sentences
(blueprint: lem-weil-pbc-idempotent-endomorphism-image-base-change).

Proof: Put `q = 1 - p`. The identities `q² = q`, `pq = qp = 0`, and `p + q = 1`
decompose every vector as `p v + q v`. Applying `p` to a vector in both images makes
it zero, and `q v = v` on the kernel of `p`. Thus the images are complementary and
`range q = ker p`. A direct summand of a finite free module is finite projective.
Tensor this split decomposition with `S`. The split inclusions and projections remain
split, and the tensor universal property identifies the first inclusion with
`s ⊗ v ↦ s • ρ(v)` (lem-weil-pbc-module-base-change-universal-property).
The hypothesis `p ∘ p = p` is `IsIdempotentElem p` in `Module.End R (Fin n → R)`, whose
multiplication is composition; likewise for `p_S`.
The matrix of the tensor projector is the entrywise image of the original matrix.
It is identity on the first tensor summand and zero on the second. Hence it is
idempotent, and its range is exactly the injective image of the first tensor summand.
The resulting range equivalence is the displayed canonical map. The tensor factors
are ordered `S ⊗[R] range p`, using the canonical commutor to express `range p ⊗[R] S`.
-/
theorem idempotent_image_baseChange
    {R : Type u} [CommRing R] (n : ℕ)
    (p : Module.End R (Fin n → R)) (hp : IsIdempotentElem p)
    {S : Type v} [CommRing S] (ρ : R →+* S) :
    letI : Algebra R S := ρ.toAlgebra
    let pS : Module.End S (Fin n → S) :=
      Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)
    IsCompl p.range (1 - p).range ∧
      (1 - p).range = p.ker ∧
      Module.Finite R p.range ∧ Module.Projective R p.range ∧
      IsIdempotentElem pS ∧
      ∃ f : S ⊗[R] p.range →ₗ[S] (Fin n → S),
        (∀ (s : S) (x : p.range), f (s ⊗ₜ[R] x) = fun i ↦ s * ρ (x.val i)) ∧
        Function.Injective f ∧ f.range = pS.range ∧
        ∃ e : S ⊗[R] p.range ≃ₗ[S] pS.range,
          pS.range.subtype.comp e.toLinearMap = f := by
  sorry

end LinearMap
