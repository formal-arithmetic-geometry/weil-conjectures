/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Finite algebras over a local ring with étale retractions

Source: `literature/stacks-project/algebra.tex`, Lemma Tag 04GG (proof of 8 => 10)
(blueprint: lem-weil-pbc-etale-retraction-finite-product-local).
-/

universe u v

/-- Over a local ring for which pointed étale neighborhoods admit retractions, every
finite algebra is a finite product of local rings.

Source: Stacks Project, algebra.tex, Lemma Tag 04GG, proof of (8) => (10).
The proof follows the six steps of the node:

1. Apply `lem-weil-pbc-finite-algebra-etale-idempotent-decomposition` (Tag 00UK,
   finite case Tag 00UL) to `R → B` at the maximal ideal. Obtain an étale `R'`, a
   prime `p` over that ideal with bijective residue-field map, and complete
   orthogonal idempotents `e₁, …, eₙ, e∞` in `C = R' ⊗[R] B`. Every prime over
   `p` contains `e∞`, and at most one such prime misses each `eᵢ`.
2. Apply `hR` to obtain the retraction `τ` with the prescribed maximal-ideal comap.
3. The tensor-product universal property gives the surjection `φ : C → B` sending
   `r' ⊗ b` to `τ(r') • b`. A prime of `B` over the maximal ideal pulls back to a
   prime of `C` over `p`; surjectivity recovers the original prime from its preimage.
4. The images `fᵢ = φ(eᵢ)` and `f∞ = φ(e∞)` are complete orthogonal idempotents.
   Every prime of `B` over the maximal ideal contains `f∞`; at most one misses `fᵢ`.
5. For an idempotent `f`, the factor `fB`, with unit `f`, is a finite quotient of
   `B`. Its primes correspond to primes of `B` missing `f`. By
   `lem-weil-pbc-finite-algebra-local-radical`, every maximal ideal of this finite
   algebra lies over the maximal ideal of `R`. Hence `f∞B = 0`, since otherwise it
   would have a maximal ideal. Each nonzero `fᵢB` has exactly one maximal ideal,
   and is therefore a local ring.
6. Discard the zero `fᵢ`. The remaining orthogonal idempotents sum to `1`, giving
   the algebra isomorphism `b ↦ (fᵢb)`, with inverse the sum of the components.
   If `B` is zero, no factors remain and the product is empty.

(blueprint: lem-weil-pbc-etale-retraction-finite-product-local) -/
theorem finite_algebra_is_product_local_rings
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : ∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R'],
      Algebra.Etale R R' →
        ∀ (p : Ideal R') [p.IsPrime],
          ∀ (hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R),
            Function.Bijective
                (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
                  (Algebra.ofId R R') hp.symm) →
              ∃ (τ : R' →ₐ[R] R),
                p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom)
    {B : Type v} [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (n : ℕ) (A : Fin n → Type v)
      (comm : ∀ i, CommRing (A i))
      (alg : ∀ i, Algebra R (A i))
      (loc : ∀ i, IsLocalRing (A i)),
      letI : ∀ i, CommRing (A i) := comm
      letI : ∀ i, Algebra R (A i) := alg
      letI : ∀ i, IsLocalRing (A i) := loc
      Nonempty (B ≃ₐ[R] ∀ i, A i) := by
  sorry
