/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: N5
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularLocalPicardZero
import Sheaf.TraceFormula.NagataInvertPrime

/-!
# Boundary-unit factorization in a regular local ring

Source: Stacks Project, more-algebra.tex, Tag 0AG0, lemma-regular-local-UFD
(blueprint: lem-trf-regular-local-ufd-boundary-factorization).
-/

@[expose] public section

open scoped BigOperators

universe u

/-- A regular local ring is a domain and a UFD; selected members of a regular parameter
system are prime, and they are exactly the possible non-unit factors after inverting their
product. Source: Stacks Project, more-algebra.tex, Tag 0AG0, lemma-regular-local-UFD
(blueprint: lem-trf-regular-local-ufd-boundary-factorization).

Proof: use the regular-local domain theorem and the regular-parameter hypersurface criterion to
show that each selected parameter is prime. Induct on the dimension, localizing at a parameter
and applying the regular-local UFD induction hypothesis, then descend primality with Nagata's
criterion to obtain `UniqueFactorizationMonoid A`. In that UFD, a unit in the localization at the
product has no prime factors except the selected parameters, giving the displayed factorization;
the converse follows by choosing a common denominator. The argument permits `r = 0`, when the
product is `1` and the assertion reduces to being a unit in `A`.
-/
theorem regularLocalUFDBoundaryFactorization (A : Type u) [CommRing A]
    [IsRegularLocalRing A]
    (t : List A) (ht : IsLocalRing.IsRegularSystemOfParameters t)
    (r : ℕ) (ι : Fin r → Fin t.length) (hι : Function.Injective ι) :
    IsDomain A ∧ UniqueFactorizationMonoid A ∧
      (∀ i : Fin r, Prime (t.get (ι i))) ∧
      (∀ f : A,
        IsUnit (algebraMap A (Localization.Away (∏ i : Fin r, t.get (ι i))) f) ↔
          ∃ u : A, IsUnit u ∧ ∃ a : Fin r → ℕ,
            f = u * ∏ i : Fin r, (t.get (ι i)) ^ (a i)) := by
  sorry

end
