/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! # Total quotient ring as a product over minimal primes

Source: literature/stacks-project/algebra.tex, Algebra Lemma 10.25.4, tag 02LX,
with Definition 10.66.1, tag 0547, and Lemma 10.66.7, tag 05C3
(blueprint: lem-sc-affine-totalquotient-minimal-product)
-/

@[expose] public section

universe u

namespace Algebra

/-- The canonical total quotient ring decomposition for finitely many minimal primes,
when every weakly associated prime is minimal. The equivalence `q` enumerates all
minimal primes exactly once. The colon ideal `(⊥ : Submodule A A).colon {a}` is the
annihilator `{r | r * a = 0}` of `a`, and weak association is membership in its minimal
primes, as in `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`. Thus `hweak` states
the weak-association hypothesis of Definition 10.66.1 (tag 0547), without an
unspecified predicate. An `A`-algebra equivalence necessarily sends each fraction to
its images in the prime localizations: it fixes the images of numerators and maps
inverses of denominators to inverses.

Source: literature/stacks-project/algebra.tex, Algebra Lemma 10.25.4, tag 02LX,
with Definition 10.66.1, tag 0547, and Lemma 10.66.7, tag 05C3
(blueprint: lem-sc-affine-totalquotient-minimal-product)

Proof:
1. By `lem-sc-affine-weakass-nonzerodivisors`, zero-divisors form the union of the
weakly associated primes. By `hweak` and `lem-pc-minimal-prime-avoids-nonzerodivisor`,
this is exactly the union of the minimal primes. Non-zero-divisors avoid every factor's prime.
2. The localization universal property (`def-weil-pbc-module-localization` and
`def-weil-pbc-localization-at-prime`) gives the canonical map to each factor and their product.
3. By `lem-weil-pbc-localization-prime-residue-field-iso`, primes of the total quotient
ring correspond to primes disjoint from non-zero-divisors. By
`lem-weil-pbc-prime-avoidance` and minimality, these are exactly the listed primes;
minimality also shows that their extensions are maximal.
4. By `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, their intersection is the nilradical,
so every element of the Jacobson radical is nilpotent. Apply
`lem-weil-pbc-product-of-localizations-at-maximal` to obtain the product decomposition.
5. By `lem-weil-pbc-localization-prime-residue-field-iso`, the factors identify with
`A` localized at the corresponding minimal primes, compatibly with the maps from `A`.
Uniqueness in step 2 identifies the resulting equivalence with the canonical map. -/
theorem totalQuotientRing_isProduct_minimalPrimes
    {A : Type u} [CommRing A] {t : ℕ}
    (q : Fin t ≃ {p : PrimeSpectrum A // p.asIdeal ∈ minimalPrimes A})
    (hweak : ∀ (a : A) (p : Ideal A),
      p ∈ ((⊥ : Submodule A A).colon {a}).minimalPrimes →
        p ∈ minimalPrimes A) :
    Nonempty (Localization (nonZeroDivisors A) ≃ₐ[A]
      (∀ i : Fin t, Localization.AtPrime (q i).val.asIdeal)) := by
  sorry

end Algebra
