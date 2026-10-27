/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Matching a contracted prime family with parameter factors

Source: Stacks Project, More on Algebra, Tag 0AG0, opening parameter-primality argument;
agent prime-family matching argument, steps 4--6 of the returned parent
`lem-trf-etale-component-coordinate-identification`
(blueprint: lem-trf-parameter-product-prime-family-matching).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace IsLocalRing

/-- A finite prime family with distinct minimal contractions and the same closed union as a
parameter product has a unique labeling by its parameter factors.

Source: Stacks Project, More on Algebra, Tag 0AG0, opening parameter-primality argument;
agent prime-family matching argument in returned parent steps 4--6
(blueprint: lem-trf-parameter-product-prime-family-matching).

Proof:
1. Clause (b) of `lem-sfb-transverse-prime-ideal-parameters` makes the initial parameter
ideals pairwise incomparable proper primes and identifies them with the minimal primes of
their product ideal. This includes the empty product.
2. If `r = 0`, the product is one and its zero locus is empty. Each proper prime `q a`
belongs to its own zero locus, so the assumed closed-set equality forces the family empty.
The empty equivalence is then the unique matching.
3. For any `a`, the equality of zero loci puts the product in `q a`. Primality supplies a
parameter prime `P i` contained in `q a`. Conversely `P i` contains the product, so the same
equality supplies `b` with `q b ≤ P i`. Contract the chain `q b ≤ P i ≤ q a` to obtain
`I ≤ p b ≤ p a`. Minimality of `p a` gives equality of the contractions, and their distinctness
gives `b = a`. Thus `q a = P i`.
4. Incomparability makes this index unique. If two labels have the same parameter prime,
contraction and distinctness of the `p a` make those labels equal, proving injectivity.
5. Each parameter prime contains the product, so it contains some `q a = P (e a)`.
Incomparability forces `e a = i`, proving surjectivity. Distinctness of the parameter ideals
forces every other matching equivalence to agree pointwise, proving uniqueness.
-/
theorem parameterProductPrimeFamilyMatching
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsRegularLocalRing R]
    (φ : A →+* R) {d r : ℕ} (t : Fin d → R)
    (ht : IsRegularSystemOfParameters (List.ofFn t)) (hr : r ≤ d)
    (I : Ideal A) (F : Type w) [Finite F] (p : F → Ideal A) (q : F → Ideal R)
    (hp : ∀ a : F, p a ∈ I.minimalPrimes) (hp_distinct : Function.Injective p)
    (hq : ∀ a : F, (q a).IsPrime) (hcontraction : ∀ a : F, Ideal.comap φ (q a) = p a)
    (hV : PrimeSpectrum.zeroLocus
        (Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)} : Set R) =
      ⋃ a : F, PrimeSpectrum.zeroLocus (q a : Set R)) :
    (∀ i : Fin r, (Ideal.span {t (Fin.castLE hr i)}).IsPrime) ∧
    (Pairwise fun i j : Fin r ↦
      ¬ Ideal.span {t (Fin.castLE hr i)} ≤ Ideal.span {t (Fin.castLE hr j)}) ∧
    (Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)}).minimalPrimes =
      Set.range (fun i : Fin r ↦ Ideal.span {t (Fin.castLE hr i)}) ∧
    (∃! e : F ≃ Fin r, ∀ a : F, q a = Ideal.span {t (Fin.castLE hr (e a))}) ∧
    (r = 0 → IsEmpty F) := by
  sorry

end IsLocalRing
