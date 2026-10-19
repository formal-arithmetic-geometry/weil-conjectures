/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Generic localization of a birational affine map

Source: Stacks Project, Morphisms of Schemes, Tag 0BAB,
`lemma-birational-generic-fibres`, the affine-ring paragraph
(blueprint: lem-per-birational-generic-localization).
-/

@[expose] public section

universe u v

namespace Localization

/-- A ring map with unique minimal primes and an isomorphism on the corresponding local
rings induces an isomorphism after localizing the target at the image of the complement
of the source minimal prime. The conclusion is bijectivity of the canonical fraction map,
not merely the existence of an abstract ring isomorphism.

Source: Stacks Project, Morphisms of Schemes, Tag 0BAB,
`lemma-birational-generic-fibres`, the affine-ring paragraph
(blueprint: lem-per-birational-generic-localization).

Proof:
1. Write S = B minus q, W = φ(S), and C = W⁻¹A. The contraction hypothesis makes W
   disjoint from p. The canonical fraction maps θ : B_q → C and ψ : C → A_p satisfy
   ψθ = h, the given local-ring isomorphism (def-weil-pbc-localization-at-prime).
2. The localization prime correspondence gives the prime J = pC and identifies its
   contraction with p; it also identifies the contraction of pA_p with p
   (lem-weil-pbc-localization-prime-residue-field-iso, clause 1).
3. The composite C → A_p → κ(p) is surjective, since its composite with θ is the
   isomorphism h followed by the residue quotient. A fraction has zero residue exactly
   when its numerator lies in p, by step 2. Its kernel is therefore J. Hence J is maximal:
   if I strictly contains J, take x in I outside J and lift the inverse of its nonzero
   residue to y; then 1 - xy belongs to J and consequently 1 belongs to I.
4. Any prime P of C contracts to a prime Q of A and equals QC by the correspondence.
   Every prime contains a minimal prime (lem-weil-pbc-prime-contains-minimal-prime).
   Since p is the unique minimal prime of A, p is contained in Q, so J is contained in P.
5. Since J is maximal and every prime contains it, it is the only prime of C.
6. For t outside p, its image in C is outside J. If that image were a nonunit, its
   proper principal ideal would be contained in a maximal ideal
   (lem-weil-pbc-proper-ideal-contained-in-maximal). Such an ideal is prime, so equals J,
   a contradiction. Thus every such t becomes a unit.
7. Define η : A_p → C by a/t ↦ λ(a)λ(t)⁻¹. The fraction equality criterion and the
   units of step 6 make this well defined and a ring map. On fractions, ψη and ηψ are
   identities. Thus ψ is an isomorphism, and θ = ψ⁻¹h is an isomorphism as required. -/
theorem generic_localization_bijective_of_unique_minimalPrimes
    {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    (φ : B →+* A) (q : PrimeSpectrum B) (p : PrimeSpectrum A)
    (hq : minimalPrimes B = {q.asIdeal}) (hp : minimalPrimes A = {p.asIdeal})
    (hqp : q.asIdeal = p.asIdeal.comap φ)
    (hlocal : Function.Bijective (localRingHom q.asIdeal p.asIdeal φ hqp)) :
    Function.Bijective
      (IsLocalization.map (Localization (q.asIdeal.primeCompl.map φ)) φ
        q.asIdeal.primeCompl.le_comap_map :
        Localization.AtPrime q.asIdeal →+* Localization (q.asIdeal.primeCompl.map φ)) := by
  sorry

end Localization
