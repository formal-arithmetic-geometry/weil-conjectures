/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Finite-type splitting from étale retractions

Source: Stacks Project, Algebra, Lemma Tag 04GG, proof of (8) ⇒ (11), using Tag 00UK
(blueprint: lem-weil-pbc-etale-retraction-finite-type-splitting).
-/

universe u v

namespace Algebra

/--
Source: Stacks Project, Algebra, Lemma Tag 04GG, proof of (8) ⇒ (11)
(blueprint: lem-weil-pbc-etale-retraction-finite-type-splitting).

Assuming that every étale algebra with a rational point over the closed point
retracts to the local ring, a finite-type algebra splits into a finite factor
and a factor with no quasi-finite point above the maximal ideal.

Proof:
1. Apply `lem-weil-pbc-finite-type-etale-finite-factor-decomposition` (Stacks 00UK)
   to `R → S` at the maximal ideal. It gives an étale `R → R'`, a prime `m'` over
   the maximal ideal with the same residue field, and `R' ⊗[R] S ≅ A' × B'`,
   with `A'` finite and no quasi-finite point of `B'` over `m'`.
2. Apply the retraction hypothesis to obtain `τ : R' →ₐ[R] R` with inverse image
   of the maximal ideal equal to `m'` (the source prints this equality backwards).
3. Set `A = A' ⊗[R', τ] R` and `B = B' ⊗[R', τ] R`. Tensor cancellation and
   preservation of the two-factor product give `S ≅ A × B`. Tensoring finite
   module generators of `A'` gives finite generators of `A`. The product
   projection makes `B` a quotient of `S`, hence a finite-type `R`-algebra.
4. The residue-field map induced by `τ` is inverse to the original residue-field
   isomorphism (`def-weil-residue-field`), so tensor cancellation identifies
   `B ⊗[R] κ` with `B' ⊗[R'] κ(m')`. The corresponding fibre spectra are
   homeomorphic, with their points corresponding to primes over the respective
   base primes. By `def-weil-pbc-ring-map-quasi-finite-at-prime`, quasi-finiteness
   is isolatedness in the fibre. No point on the second fibre is isolated, so
   neither is any point on the first.

The factors are allowed in the same universe as `S`, including zero rings. The
étale test algebras range over `Type (max u v)`, as in
`finite_algebra_is_product_local_rings`: an étale `R`-algebra is essentially small
over `R`, so this universe holds every one the proof needs, whereas a test universe
smaller than that of `R` could leave the hypothesis vacuous.
-/
theorem etale_retraction_finite_type_splitting
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : ∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R'],
      Algebra.Etale R R' →
        ∀ (p : Ideal R') [p.IsPrime],
          ∀ (hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R),
            Function.Bijective
                (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
                  (Algebra.ofId R R') hp.symm) →
              ∃ (τ : R' →ₐ[R] R),
                p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom)
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (A B : Type v) (_ : CommRing A) (_ : CommRing B)
      (_ : Algebra R A) (_ : Algebra R B) (_ : Algebra.FiniteType R B),
      (∃ e : S ≃ₐ[R] A × B,
        Module.Finite R A ∧
          (∀ q : PrimeSpectrum B,
            q.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
              ¬ IsQuasiFiniteAtPrime R B q)) := by
  sorry

end Algebra
