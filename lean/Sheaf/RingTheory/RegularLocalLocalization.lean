/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Localization of a regular local ring

Source: literature/stacks-project/algebra.tex, Lemma Tag 0AFS and Definition Tag 00OD
(blueprint: lem-weil-pbc-regular-local-localization)
-/

universe u

namespace IsRegularLocalRing

/-- A prime localization of a regular local ring is regular local, and the ring is regular.
Source: Stacks Project, Algebra, Lemma Tag 0AFS and Definition Tag 00OD
(blueprint: lem-weil-pbc-regular-local-localization).

Proof:
1. `R` is Noetherian by regularity. Its localization at the complement of `p` is Noetherian
   by `lem-weil-pbc-localization-noetherian` and local by
   `def-weil-pbc-localization-at-prime`, with maximal ideal the extension of `p`.
2. By `lem-weil-pbc-regular-local-finite-gl-dim`, `R` has global dimension at most its
   Krull dimension, hence finite global dimension (`def-weil-pbc-finite-global-dimension`).
3. By `lem-weil-pbc-localization-finite-gl-dim`, this bound is preserved upon localization
   at the complement of `p`, so `Localization.AtPrime p` has finite global dimension.
4. Apply `lem-weil-pbc-finite-gl-dim-regular-local` to this Noetherian local ring to obtain
   the first assertion.
5. Repeat for every prime. Together with Noetherianity of `R`, this is `IsRegularRing R`
   by `def-weil-regular-scheme` (Stacks Definition Tag 00OD). At the maximal ideal,
   the localization is isomorphic to `R`, consistently with its original regularity. -/
theorem localization_at_prime_and_isRegularRing
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) ∧ IsRegularRing R := by
  sorry

end IsRegularLocalRing
