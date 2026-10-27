/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import WeilConjectures.RingTheory.CompletionMapForLocalHom

/-!
# Generator congruences and localization

Source: Stacks Project, `more-morphisms.tex`, Tag 0CAU, proof of lemma-map-approximation.
(blueprint: lem-trf-generator-congruence-localization)

The finite polynomial ring is represented by `MvPolynomial (Fin n) R`, canonically
isomorphic to the n-fold iterated one-variable polynomial ring. The completion map
is selected from its coordinate characterization, which uniquely determines it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

universe u v w

namespace RingHom

/-- Congruences on finitely many generators determine the marked prime and extend to fractions.
Source: Stacks Project, `more-morphisms.tex`, Tag 0CAU, proof of lemma-map-approximation,
the map from the presented algebra to A' and the final marked-point assertion.
(blueprint: lem-trf-generator-congruence-localization)

Proof:
1. Evaluate polynomials at b. Since every relation vanishes, evaluation descends through
   the ideal spanned by the relations. Polynomial extensionality gives uniqueness on the
   quotient (`def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-algebra-hom-quotient`).
2. Localizations of A and A' are Noetherian (`lem-weil-pbc-localization-noetherian`). Their
   completions are local, with maximal ideals equal to the kernels of coordinate one
   (`lem-weil-pbc-local-completion-local-ring`). Since N is positive, J lies in this kernel.
3. The coordinate characterization in `lem-weil-pbc-fs-adic-completion-map-local` makes the
   induced completion map compatible with the residue-field map and the original maps.
   The residue-field map is injective, being a unital map of fields. Thus the completion
   map reflects membership in the maximal ideal and respects the R-algebra structures.
4. Reduce the two polynomial maps modulo J. They agree on coefficients and generators,
   hence on all polynomials by `def-weil-pbc-mv-polynomial-ring`, and then on their quotient.
5. A numerator lies in a prime iff its image in the prime localization is in the maximal
   ideal (`def-weil-pbc-localization-at-prime`). Use locality of theta, step 3, and congruence
   modulo J inside the target maximal ideal to identify the inverse-image prime with q.
6. Localize phi at these primes: r/s maps to phi(r)/phi(s). Clearing denominators proves
   well-definedness, and the numerator criterion proves that this induced map is local.
7. For a fraction r/s, both denominator images U,V are units. The identity
   f(r)/U - g(r)/V = (f(r)-g(r))/U + g(r)*(V-U)/(U*V) puts the difference in J, by step 4.
   Ring maps preserve inverses of units, so this proves the asserted congruence for all z.
-/
theorem exists_unique_generator_congruence_localization
    {R : Type u} {A : Type v} {A' : Type w}
    [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [IsNoetherianRing A] [IsNoetherianRing A']
    (h : A →ₐ[R] A') (p : Ideal A) (p' : Ideal A') [p.IsPrime] [p'.IsPrime]
    (hp : Ideal.comap h.toRingHom p' = p)
    (n m : ℕ) (F : Fin m → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range F))) [q.IsPrime]
    (θ : Localization.AtPrime q →ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p)) [IsLocalHom θ]
    (N : ℕ) (hN : 1 ≤ N) (b : Fin n → A')
    (hF : ∀ j : Fin m, MvPolynomial.aeval b (F j) = 0)
    (hb : ∀ i : Fin n,
      Classical.choose (RingHom.exists_adicCompletion_map_of_local
          (Localization.localRingHom p p' h.toRingHom hp.symm))
        (θ (algebraMap _ (Localization.AtPrime q)
          (Ideal.Quotient.mk (Ideal.span (Set.range F)) (MvPolynomial.X i)))) -
        algebraMap (Localization.AtPrime p')
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
            (Localization.AtPrime p')) (algebraMap A' (Localization.AtPrime p') (b i)) ∈
        Ideal.map (algebraMap (Localization.AtPrime p')
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
            (Localization.AtPrime p')))
          ((IsLocalRing.maximalIdeal (Localization.AtPrime p')) ^ N)) :
    ∃ φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range F)) →ₐ[R] A',
      (∀ i : Fin n, φ (Ideal.Quotient.mk (Ideal.span (Set.range F))
        (MvPolynomial.X i)) = b i) ∧
      (∀ ψ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range F)) →ₐ[R] A',
        (∀ i : Fin n, ψ (Ideal.Quotient.mk (Ideal.span (Set.range F))
          (MvPolynomial.X i)) = b i) → ψ = φ) ∧
      (∀ H : MvPolynomial (Fin n) R,
        Classical.choose (RingHom.exists_adicCompletion_map_of_local
            (Localization.localRingHom p p' h.toRingHom hp.symm))
          (θ (algebraMap _ (Localization.AtPrime q)
            (Ideal.Quotient.mk (Ideal.span (Set.range F)) H))) -
          algebraMap (Localization.AtPrime p')
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
              (Localization.AtPrime p'))
            (algebraMap A' (Localization.AtPrime p')
              (φ (Ideal.Quotient.mk (Ideal.span (Set.range F)) H))) ∈
          Ideal.map (algebraMap (Localization.AtPrime p')
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
              (Localization.AtPrime p')))
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p')) ^ N)) ∧
      ∃ hφ : q = Ideal.comap φ.toRingHom p',
        IsLocalHom (Localization.localAlgHom q p' φ hφ) ∧
        ∀ z : Localization.AtPrime q,
          Classical.choose (RingHom.exists_adicCompletion_map_of_local
              (Localization.localRingHom p p' h.toRingHom hp.symm)) (θ z) -
            algebraMap (Localization.AtPrime p')
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
                (Localization.AtPrime p')) (Localization.localAlgHom q p' φ hφ z) ∈
            Ideal.map (algebraMap (Localization.AtPrime p')
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
                (Localization.AtPrime p')))
              ((IsLocalRing.maximalIdeal (Localization.AtPrime p')) ^ N) := by
  sorry

end RingHom
