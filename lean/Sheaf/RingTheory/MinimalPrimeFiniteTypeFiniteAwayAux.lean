/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum

/-! An explicit finite spanning family after shrinking at a minimal prime.
(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux)
-/

@[expose] public section

universe u v

namespace RingHom

/-- The coefficient-lifting and monic-polynomial argument for generic finiteness produces
an explicit finite spanning family after one principal localization.  This is the strict
finite-spanning intermediate form used by the generic-finiteness theorem.

Source: Stacks Project, Algebra, Tag 02ML, `lemma-generically-finite`.  The proof chooses
finite algebra generators, obtains monic equations in the localization at the minimal
prime from finite-dimensionality of the fibre, clears their finitely many denominators,
and reduces monomials by those equations.

(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux).

Proof: The finite-spectrum fibre theorem gives finite-dimensionality over the residue field.
Lift monic annihilating equations through the prime localization, use local nilpotence of the
extended minimal prime to obtain powers that vanish, clear the finitely many denominators and
annihilators by multiplying an element outside the prime, and reduce monomials by the resulting
monic equations. -/
theorem exists_finite_span_awayMap_of_finite_fiber_minimalPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.FiniteType) (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite) :
    ∃ g : R, g ∉ p ∧
      letI : Algebra (Localization.Away g) (Localization.Away (φ g)) :=
        (Localization.awayMap φ g).toAlgebra
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away (φ g),
        Submodule.span (Localization.Away g) (Set.range b) = ⊤ := by
  sorry

end RingHom
