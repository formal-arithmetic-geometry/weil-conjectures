/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizations of Nagata rings

Source: Stacks Project, Algebra, Lemma 10.162.6 (Tag 032U), `lemma-nagata-localize`
(blueprint: lem-weil-pbc-nagata-localization).
-/

@[expose] public section

universe u

/-- A localization of a Nagata ring is Nagata, including the localizations at prime ideals
and the principal localizations. `IsNagataRing` asserts both Noetherianity and the N-2
property of every prime quotient.
Source: Stacks Project, Algebra, Lemma 10.162.6 (Tag 032U)
(blueprint: lem-weil-pbc-nagata-localization).

Proof:
1. By `def-weil-pbc-nagata-ring`, `A` is Noetherian. Its localization is Noetherian by
   `lem-weil-pbc-localization-noetherian`.
2. For a prime `q` of the localization, its inverse image `p` in `A` is prime and disjoint
   from `T`. By `lem-weil-pbc-localization-quotient-by-prime`, the quotient by `q` is
   isomorphic to the localization of `A / p` at the image of `T`, which does not contain zero.
3. The Nagata hypothesis makes `A / p` N-2. By `lem-weil-pbc-localization-n2-domain` its
   localization is N-2. Transport this property through the isomorphism in step 2: identify
   the fraction fields, restrict each finite field extension along this identification,
   identify the integral closures, and transport finite generation of the resulting modules.
   This gives the N-2 clause of `def-weil-pbc-japanese-domain` for the quotient by `q`.
4. Steps 1--3 give `IsNagataRing`. For the particular cases use the multiplicative subsets
   `p.primeCompl` (`def-weil-pbc-localization-at-prime`) and `Submonoid.powers f`
   (`def-weil-ring-localization-away`). -/
theorem isNagataRing_localization (A : Type u) [CommRing A] (T : Submonoid A)
    (hA : IsNagataRing A) :
    IsNagataRing (Localization T) ∧
      (∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p)) ∧
      (∀ f : A, IsNagataRing (Localization.Away f)) := by
  sorry
