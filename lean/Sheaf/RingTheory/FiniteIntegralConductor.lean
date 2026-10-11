/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# A conductor power for a finite intermediate ring

Source: Stacks Project, Varieties, Lemma 33.37.5 (Tag 09N2), finite-conductor paragraph
(blueprint: lem-sc-finite-integral-conductor).
-/

@[expose] public section

universe u v

namespace Subalgebra

/-- A finite intermediate algebra in the fraction field of a Noetherian semilocal domain of
Krull dimension one contains the product of a positive power of the base ring's Jacobson radical
with the intermediate algebra. Membership in the base ring is expressed through its algebra map.
Source: Stacks Project, Varieties, Lemma 33.37.5 (Tag 09N2), finite-conductor paragraph
(blueprint: lem-sc-finite-integral-conductor).

Proof: (1) The quotient module `M = A/B` is finite. Its localization at the generic prime is
zero, since `A` and `B` have the same fraction field. (2) Every prime in its support is thus
nonzero, hence maximal by dimension one. By `lem-weil-pbc-finite-module-support-annihilator`,
the support is `V(J)`, where `J` is its annihilator. The radical of `J` is the intersection of
these primes by `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, and therefore contains the
intersection of all maximal ideals, the Jacobson radical of `B`. This radical is finitely
generated since `B` is Noetherian. By `lem-weil-pbc-fg-ideal-radical-power`, a positive power
of it is contained in `J`. (3) That power annihilates `A/B`, so its products with elements of
`A` belong to `B`. Sums of these products belong to `B` as well, giving the stated containment. -/
theorem exists_jacobson_pow_mul_mem_base
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K] :
    ∃ n : ℕ, 0 < n ∧ ∀ b : B, b ∈ (Ideal.jacobson (⊥ : Ideal B)) ^ n →
      ∀ a : A, ∃ c : B, algebraMap B K c = algebraMap B K b * (a : K) := by
  sorry

end Subalgebra
