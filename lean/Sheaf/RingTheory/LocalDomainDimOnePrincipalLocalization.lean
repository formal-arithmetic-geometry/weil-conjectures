/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A principal localization of a one-dimensional local domain is its fraction field

Source: Stacks Project, Algebra, Lemmas Tags 00CM and 00C8
(blueprint: lem-sc-local-domain-dim-one-principal-localization-fraction-field).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Let `B` be a local domain of Krull dimension one with fraction field `K`, and let
`0 ≠ f` lie in the maximal ideal of `B`. Then the localization map `B_f → K` (the lift of
`algebraMap B K` to `Localization.Away f`, defined since `f` maps to a unit of `K`) is an
isomorphism.
Source: Stacks Project, Algebra, Lemmas Tags 00CM and 00C8
(blueprint: lem-sc-local-domain-dim-one-principal-localization-fraction-field).

Proof:
1. Since `B` is a domain, `(0)` is prime. A nonzero prime `q` satisfies `(0) ⊊ q`, so by
   dimension one no prime lies strictly above `q`; hence `q` is maximal, and by locality
   `q = m`. The only primes of `B` are `(0)` and `m`.
2. By the prime correspondence for localization (`lem-weil-pbc-primes-of-localization`,
   with `B` local so `B_m = B`), the primes of `B_f` are the primes of `B` not containing
   `f`: `m` is excluded since `f ∈ m`, `(0)` is allowed since `f ≠ 0`. So `(0)` is the
   only prime of `B_f`.
3. `B_f` is a domain whose only prime is `(0)`, so every nonzero element is a unit and
   `B_f` is a field. The map `B_f → K` is injective (a power of `f ≠ 0` kills no nonzero
   numerator), and every fraction `a / b` with `b ≠ 0` lies in its image since the image
   of `b` in the field `B_f` is invertible. So the map is an isomorphism. -/
theorem bijective_away_lift_fractionRing_of_ringKrullDim_eq_one
    (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]
    (f : B) (hf_mem : f ∈ maximalIdeal B) (hf_ne : f ≠ 0) :
    Function.Bijective
      (IsLocalization.Away.lift (S := Localization.Away f) f (g := algebraMap B K)
        (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hf_ne))) := by
  sorry

end IsLocalRing
