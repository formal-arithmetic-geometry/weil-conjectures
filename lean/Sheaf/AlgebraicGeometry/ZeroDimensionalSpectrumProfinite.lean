/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Zero-dimensional affine spectra are profinite

Source: Stacks Project, Tag 04MG, `lemma-ring-with-only-minimal-primes`, implication
(6) to (1), (2), (3) (blueprint: lem-weil-pbc-zero-dimensional-spectrum-profinite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- If every prime ideal is maximal, the Zariski spectrum is compact, Hausdorff and totally
 disconnected. Source: Stacks Project, Tag 04MG, `lemma-ring-with-only-minimal-primes`
 (blueprint: lem-weil-pbc-zero-dimensional-spectrum-profinite).

Proof plan:
1. Every prime is minimal: a prime contained in it is maximal, so the inclusion is equality.
2. For `g ∈ p`, the radical-localization theorem
   (`lem-weil-pbc-minimal-prime-localization-radical`) applied to the zero ideal says `g/1`
   is nilpotent in `A_p`. The fraction relation of `def-weil-pbc-localization-at-prime`
   gives `s ∉ p` and a positive `n` with `s * g^n = 0`.
3. Consequently `D(s)` contains `p` and misses `D(g)`. The complement of each `D(g)`
   is open, so every standard open is clopen.
4. Distinct primes are separated by a standard open and its complement. These are
   disjoint open neighbourhoods, proving Hausdorffness. The same clopen separation
   prevents any connected subset from containing two distinct points, proving total
   disconnectedness.
5. `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`, clause (iii), supplies
   compactness for every commutative ring. These three properties mean profiniteness.
   The argument also includes the zero ring, whose spectrum is empty. -/
theorem Spec.profinite_of_isMaximal (A : Type u) [CommRing A]
    (h : ∀ p : Ideal A, p.IsPrime → p.IsMaximal) :
    CompactSpace (Spec (CommRingCat.of A)) ∧
      T2Space (Spec (CommRingCat.of A)) ∧
      TotallyDisconnectedSpace (Spec (CommRingCat.of A)) := by
  sorry

end AlgebraicGeometry
