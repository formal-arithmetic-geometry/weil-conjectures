/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Inertia groups and unramified intermediate extensions

Let `T / S / R` be a tower of domains, `G` a finite Galois group of `T / R` and `H ≤ G` a Galois
group of `T / S`. If the inertia group `I_G(P)` of a prime `P` of `T` is contained in `H`, then
the prime `P ∩ S` of `S` is unramified over `R`
(`Ideal.ramificationIdx_under_eq_one_of_inertia_le`): the inertia groups of `P` in `G` and `H`
then coincide, and their orders are the ramification indices `e(P | R)` and `e(P | S)`, while
`e(P | R) = e(P ∩ S | R) e(P | S)`.
-/

@[expose] public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] [IsDomain R] [IsDomain S] [IsDomain T]
  [Module.Finite R T] [Module.Finite S T] [Module.Flat R T] [Module.Flat S T]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
  (H : Subgroup G) [IsGaloisGroup H S T]

/-- **Primes below the inertia field are unramified.** If the inertia group of a prime `P` of
`T` in `Gal(T / R)` is contained in `Gal(T / S)`, then `P ∩ S` is unramified over `R`. -/
theorem ramificationIdx_under_eq_one_of_inertia_le (p : Ideal R) [p.IsPrime] (P : Ideal T)
    [P.IsPrime] [P.LiesOver p] [PerfectField p.ResidueField]
    [PerfectField (P.under S).ResidueField] (h : P.inertia G ≤ H) :
    (P.under S).ramificationIdx R = 1 := by
  have hG : Nat.card (P.inertia G) = P.ramificationIdx R := by
    rw [card_inertia_eq_ramificationIdxIn p P, ramificationIdxIn_eq_ramificationIdx p P G]
  have hH : Nat.card (P.inertia H) = P.ramificationIdx S := by
    rw [card_inertia_eq_ramificationIdxIn (P.under S) P,
      ramificationIdxIn_eq_ramificationIdx (P.under S) P H]
  have hGH : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
    have : P.inertia H = (P.inertia G).subgroupOf H := rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have htower := ramificationIdx_tower (R := R) (P.under S) P
  have hne : P.ramificationIdx R ≠ 0 := by
    rw [← hG]
    exact Nat.card_pos.ne'
  rw [← hH, hGH, hG] at htower
  exact (mul_eq_right₀ hne).1 htower.symm
