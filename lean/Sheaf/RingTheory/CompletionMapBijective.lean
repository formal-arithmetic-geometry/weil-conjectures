/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.FiniteAfterCompletion

@[expose] public section

universe u v

namespace RingHom

/-- Bijectivity of a completion map under the residue-field and maximal-ideal hypotheses.
Source: More on Algebra, Lemma Tag 0AGX, final rank-one argument.
(blueprint: lem-weil-pbc-flat-local-completion-iso-bijective)

Proof:
Let R and S denote the two completions, with maximal ideals mR and nS.
The local-completion theorem identifies these ideals with those extended from A and B,
and identifies their residue fields with the residue fields of A and B. Compatibility
and hmax therefore give mR S = nS. In particular the map sends mR into nS, hence
sends every power into the corresponding power and is adically continuous.
An element of R is congruent modulo mR^k to an element of A for every k. Thus
compatibility and separation of S identify this map with the componentwise completion
map, including its action on residue fields. The same argument identifies it with the
map supplied by finite_after_completion. Since hmax and hres identify B/mA B with
A/mA, that theorem makes S finite over R for this map.
The assumed flatness now makes S a finite free module over the local ring R.
Reduction modulo mR identifies S/mR S with B/mB, a one-dimensional vector space
over A/mA, by hres. A finite basis therefore has exactly one member e.
Write 1 = u e. If u belongs to mR then 1 belongs to mR S = nS, impossible in a
nonzero local ring. Thus u is a unit, so 1 itself is a basis. Every element of S is
then uniquely x times 1 for x in R, which says exactly that the ring map is bijective.
-/
theorem completion_map_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hmax : Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B)
    (hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge))
    (φhat : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
      AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hcomp : φhat.comp (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ)
    (hflat : φhat.Flat) : Function.Bijective φhat := by
  sorry

end RingHom
