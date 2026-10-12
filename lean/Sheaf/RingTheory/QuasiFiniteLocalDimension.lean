/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.ZariskisMainAway

/-!
# Local dimension inequality for quasi-finite ring maps

Source: Stacks Project, Algebra, Lemma 10.125.4, Tag 00QF
(blueprint: lem-weil-pbc-dimension-inequality-quasi-finite).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite-type ring map that is quasi-finite at `q` does not increase the dimension of
local rings. Source: Stacks Project, Algebra, Tag 00QF
(blueprint: lem-weil-pbc-dimension-inequality-quasi-finite).

Proof: Let `T` be the integral closure of `R` in `S` and let `q'` be the contraction of `q`
to `T` (`def-weil-pbc-integral-closure`). By the pointwise Zariski Main Theorem
(`lem-weil-pbc-integral-closure-zariski-main-away`), there is `g` in `T` outside `q'` for
which `T_g → S_g` is an isomorphism. A fraction `t/g^n` belongs to the prime induced by
`q` exactly when `t` belongs to `q'`. Localizing the isomorphism at these primes gives
`S_q ≃+* T_q'` (`lem-weil-pbc-localization-prime-residue-field-iso`), and the contraction
of `q'` to `R` is `p = q ∩ R`.

Since `T` is integral over `R`, incomparability
(`lem-weil-pbc-integral-incomparability`) sends each strict chain of primes of `T` below
`q'` to a strict chain of the same length in `R` below `p`. Local dimension is the
supremum of these lengths (`lem-weil-pbc-localization-dimension-chains-below-prime`), so
`dim T_q' ≤ dim R_p`. The ring isomorphism preserves prime chains and thus dimension;
this proves `dim S_q ≤ dim R_p`, including when dimensions are infinite. -/
theorem ringKrullDim_le_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (hq : IsQuasiFiniteAtPrime R S q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S)).asIdeal) := by
  sorry

end Algebra
