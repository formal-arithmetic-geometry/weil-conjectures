/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# A regular ring is normal

Source: Stacks Project, Algebra, Lemma Tag 0567
(blueprint: lem-weil-pbc-regular-ring-normal).
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Every localization of a regular ring at a prime ideal is a normal domain.
Source: Stacks Project, Algebra, Lemma Tag 0567
(blueprint: lem-weil-pbc-regular-ring-normal).

Proof:
1. Regularity (`def-weil-regular-scheme`) makes every prime localization regular local,
   hence in particular those at primes of height at most one. This is Serre's condition
   (R_1) (`def-weil-pbc-serre-conditions-rk-sk`).
2. For each prime localization A of dimension d, choose d generators of its maximal ideal.
   They form a regular sequence by `lem-weil-pbc-regular-local-generators-regular-sequence`
   (Tag 00NQ). They lie in the proper maximal ideal, so the definition of depth
   (`def-weil-pbc-depth`, `def-weil-pbc-regular-sequence`) gives depth A at least d,
   hence at least min(2,d). For d = 0 use the empty sequence. This is (S_2).
3. The ring is Noetherian by regularity (`def-weil-pbc-noetherian-ring`). Apply
   `lem-weil-pbc-serre-criterion-normal` (Tag 031S) to (R_1) and (S_2): each prime
   localization is a domain integrally closed in its fraction field, which is normality
   (`def-weil-pbc-normal-ring`). -/
theorem isNormalRing (R : Type u) [CommRing R] [IsRegularRing R] :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end IsRegularRing
