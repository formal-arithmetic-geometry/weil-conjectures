/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.Coset.Card

/-! # The Galois arithmetic part of normalization residue-degree divisibility

Source: Stacks Project, Tag 09EB. The geometric comparison with normalization is
supplied separately; the Galois action is an explicit hypothesis here.
-/

@[expose] public section
universe u v w
namespace AlgebraicGeometry.Scheme

/-- The residue degree of a prime in a finite flat Galois extension of domains divides
any finite group containing its Galois group as a subgroup.

Source: Stacks Project, Tag 09EB. Apply the fundamental Galois identity at the prime
under `q`. Galois transitivity identifies its common inertia degree with `q.inertiaDeg R`.
This degree divides the product of the number of primes, ramification index and residue
degree, which is the order of `T`. Lagrange's theorem then gives divisibility by `|G|`.
The finite flat domain version in Mathlib is more general than the DVR case of the source. -/
theorem normalization_residue_degree_dvd_core
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (G : Type w) [Group G] [Finite G] (T : Subgroup G)
    [MulSemiringAction T S] [IsGaloisGroup T R S]
    (q : Ideal S) [q.IsPrime] : q.inertiaDeg R ∣ Nat.card G := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (q.under R) S T
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (q.under R) q T] at h
  have hd : q.inertiaDeg R ∣ Nat.card T := by
    rw [← h, ← Nat.mul_assoc]
    exact dvd_mul_left _ _
  exact hd.trans T.card_subgroup_dvd_card

end AlgebraicGeometry.Scheme
