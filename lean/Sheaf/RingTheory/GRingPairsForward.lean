/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.LocalizationRegular
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.RegularThroughLocalization

@[expose] public section

universe u

/-- Forward implication in the G-ring criterion by pairs of primes. This is the forward
half of Stacks Project, More on Algebra, Lemma 07PN, obtained by identifying each quotient
formal fibre with the corresponding formal fibre of the localization completion.
(blueprint: lem-weil-pbc-g-ring-check-pairs-of-primes-forward) -/
theorem isGRing_pairsOfPrimes_forward (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsGRing R) :
    ∀ (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p),
      let pbar := p.map (Ideal.Quotient.mk q)
      letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
      let L := Localization.AtPrime pbar
      let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
      let F := TensorProduct (R ⧸ q) q.ResidueField C
      IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F := by
  sorry
