/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood

/-!
# Openness of the regular locus from regular prime quotients

Source: Stacks Project, More on Algebra, Tag 07P9, lemma-intersection-regular-with-closed;
Tag 07P7, definition-J (blueprint: lem-exc-regular-locus-open-from-prime-quotients).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- A Noetherian ring has open regular locus if each prime quotient has a nonempty regular open.

Source: Stacks Project, More on Algebra, Tag 07P9, lemma-intersection-regular-with-closed;
Tag 07P7, definition-J (blueprint: lem-exc-regular-locus-open-from-prime-quotients).

Proof (the seven steps of the node):
1. Put `E = {p | A_p is regular local}`. If `q ⊆ p` and `p ∈ E`, view `q A_p` as a
   prime of `A_p` using `lem-weil-pbc-primes-of-localization`. Its localization is regular
   by `lem-weil-pbc-regular-local-localization`, and is `A_q` by
   `lem-weil-pbc-localize-localization-at-prime`. Thus `E` is stable under generalization.
2. At `p ∈ E`, choose `r = dim A_p` generators of its maximal ideal
   (`def-weil-regular-scheme`). Write them as `a_i/s_i` with `a_i ∈ p`, `s_i ∉ p`.
   Since the denominators are units, the numerators still generate. They form a regular
   sequence in `A_p` by `lem-weil-pbc-regular-local-generators-regular-sequence`, also
   when `r = 0`.
3. By `lem-exc-regular-sequence-principal-neighbourhood`, there is `g ∉ p` on whose
   principal open these numerators form a regular sequence.
4. Write `p = (a_1,...,a_m)` by Noetherianity. Express each `a_j/1` in terms of the
   chosen numerators in `A_p`, clear its finitely many denominators, and multiply by an
   element outside `p` witnessing equality of fractions. This yields `s_j ∉ p` with
   `s_j a_j` in the ideal `I` of the numerators. Put `h = g ∏ s_j`. In `B = A[1/h]`,
   `p B = I B`. Localization preserves regularity: apply
   `lem-weil-pbc-localization-module-exact` to multiplication on each successive quotient
   and identify its localization with the corresponding quotient of `B`. Explicitly,
   `(c + J)/s^n` maps to `c/s^n + J B`; clearing powers of `s` proves its kernel zero
   and surjectivity is immediate from fractions. The final quotient is nonzero because
   `I B ⊆ p B`, and `h ∉ p` makes `p B` proper. This is
   `def-weil-pbc-regular-sequence`.
5. The complement of the assumed open in `Spec (A/p)` is `V(J)` by
   `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. Nonemptiness gives `J ≠ 0`.
   Choose a nonzero element of `J`, lift it to `b ∉ p`, and put `k = h b ∉ p`.
   For every `q ⊇ p` avoiding `k`, its quotient prime lies in that regular open, and
   `h ∉ q`.
6. Localize the regular sequence in `B` at such a `q`, using
   `lem-weil-pbc-weakly-regular-sequence-localization-prime` and the canonical fraction
   identification with `A_q`. Its generated ideal is `p A_q`, whose quotient is the
   regular local ring `(A/p)_(q/p)` by `lem-weil-pbc-localization-at-prime-of-quotient`.
   Since `A_q` is Noetherian by `lem-weil-pbc-localization-noetherian`, apply
   `lem-exc-regular-local-lift-regular-sequence-quotient` to conclude `q ∈ E`.
7. Steps 1 and 2--6 give the two hypotheses of
   `lem-exc-nagata-principal-open-criterion`. Hence every point of `E` lies in a principal
   open contained in `E`. Their union is `E`, so `E` is open. For the zero ring both
   the spectrum and this union are empty.
-/
theorem isOpen_regularLocus_of_primeQuotient_regularOpen
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : ∀ (p : Ideal A), p.IsPrime →
      ∃ U : Set (PrimeSpectrum (A ⧸ p)),
        IsOpen U ∧ U.Nonempty ∧
          ∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
            IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    IsOpen {q : PrimeSpectrum A |
      IsRegularLocalRing (Localization.AtPrime q.asIdeal)} := by
  sorry

end RingTheory
