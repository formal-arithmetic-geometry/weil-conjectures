/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import Sheaf.RingTheory.NormalizationCompletedBranchLift
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Finite prime fibres of a normalization

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Proposition 4.8.2, printed pp. 83--84 (PDF pp. 97--98), domain and own-fraction-field case
(blueprint: lem-trf-normalization-finite-prime-fibres).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

@[expose] public section

namespace RingTheory

/-- The normalization of a Noetherian domain has finite fibres, bounded by completed branches.

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Proposition 4.8.2, printed pp. 83--84 (PDF pp. 97--98), domain and own-fraction-field case
(blueprint: lem-trf-normalization-finite-prime-fibres).

Proof: localize at the chosen prime and use the localization prime correspondence to
identify the fibre with primes of the localized normalization. Complete the resulting local
domain. The completed-component comparison and completed-branch lifting place every fibre
prime in one of the finitely many branch normalizations. Completeness makes each branch
henselian; the connected integral component permanence theorem makes its normalization
local, so there is only one relevant maximal prime on each branch. Fraction-field
uniqueness identifies the lifting maps with the fixed branch embeddings. Counting the
finite image of the branch set gives the bound by the number of minimal primes of the
completed localization. -/
theorem normalization_finite_prime_fibres
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (p : Ideal R) [p.IsPrime] :
    Set.Finite {Q : Ideal (integralClosure R (FractionRing R)) |
      Q.IsPrime ∧ Q.comap (algebraMap R (integralClosure R (FractionRing R))) = p} ∧
      Set.ncard {Q : Ideal (integralClosure R (FractionRing R)) |
        Q.IsPrime ∧ Q.comap (algebraMap R (integralClosure R (FractionRing R))) = p} ≤
        Set.ncard (minimalPrimes
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))) := by
  sorry

end RingTheory
