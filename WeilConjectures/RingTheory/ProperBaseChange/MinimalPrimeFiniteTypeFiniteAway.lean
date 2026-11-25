/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import WeilConjectures.RingTheory.ProperBaseChange.MinimalPrimeFiniteTypeFiniteAwayAux

/-!
# Finiteness near a minimal prime

A finite-type ring map `R → S` with only finitely many primes over a minimal prime `p` of `R`
becomes finite after inverting one element `g ∉ p`.

## Implementation details

Choose algebra generators `x₁, …, xₙ` of `S`. The fibre `κ(p) ⊗[R] S = Sₚ/pSₚ` has finite
spectrum and is of finite type, hence finite-dimensional, so each `xᵢ` satisfies a monic
equation `Pᵢ(xᵢ) ∈ pSₚ` with coefficients lifted to `Rₚ`. Minimality of `p` makes `pSₚ` locally
nilpotent, so `Pᵢ(xᵢ)^eᵢ = 0`. Clearing the finitely many denominators and annihilators by a
single `g ∉ p`, the monic `Pᵢ^eᵢ` annihilate `xᵢ` in `S[φ(g)⁻¹]`, and reducing monomials gives a
finite spanning family. The cases `A = 0` and `n = 0` need no separate argument.

## References

* [Stacks, Tag 02ML]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A finite-type ring map with only finitely many primes over a minimal prime becomes
finite after inverting one element outside that prime. -/
theorem exists_finite_awayMap_of_finite_fiber_minimalPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.FiniteType) (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite) :
    ∃ g : R, g ∉ p ∧ (Localization.awayMap φ g).Finite := by
  obtain ⟨g, hg, n, b, hb⟩ :=
    exists_finite_span_awayMap_of_finite_fiber_minimalPrime φ hφ p hp hfinite
  refine ⟨g, hg, ?_⟩
  let _ : Algebra (Localization.Away g) (Localization.Away (φ g)) :=
    (Localization.awayMap φ g).toAlgebra
  change Module.Finite (Localization.Away g) (Localization.Away (φ g))
  exact ⟨Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, b, hb⟩⟩

end RingHom
