/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
# Difference of two basic constructible subsets of an affine spectrum

Source: Étale Cohomology, Lemma 59.72.1 (Tag 03S0), proof (the refinement is asserted there),
with the basic sets of Algebra, Lemma 10.29.3 (Tag 0G1P)
(blueprint: lem-weil-pbc-affine-basic-set-difference).
-/

universe u

open Set

namespace PrimeSpectrum

/-- (blueprint: lem-weil-pbc-affine-basic-set-difference)
For a commutative ring `A`, the difference `B \ C` of two basic subsets
`B = D(f) ∩ V(g₁, ..., gᵣ)` and `C = D(h) ∩ V(k₁, ..., kₛ)` of its prime spectrum is a finite
pairwise-disjoint union of basic subsets (the empty union is allowed).
`BasicConstructibleSetData.toSet` represents `D(f) ∩ V(g₁, ..., gᵣ)` as `V(g₁, ..., gᵣ) \ V(f)`.

Source: Étale Cohomology, Lemma 59.72.1 (Tag 03S0), proof; Algebra, Lemma 10.29.3 (Tag 0G1P).

Proof:
1. `V(a₁, ..., aₙ) ∩ V(b₁, ..., bₘ) = V(a₁, ..., aₙ, b₁, ..., bₘ)`, and `D(a) ∩ D(b) = D(ab)`
   because primes are prime ideals; so a finite intersection of sets `D(·)` and `V(·)` with at
   least one `D(·)` is basic.
2. A prime `𝔭` is not in `C` iff `h ∈ 𝔭` or `kⱼ ∉ 𝔭` for some `j`. So `𝔭 ∈ B \ C` iff `𝔭 ∈ B` and
   either (a) `h ∈ 𝔭`, or (b) `h ∉ 𝔭` and, for the least `j` with `kⱼ ∉ 𝔭`,
   `k₁, ..., kⱼ₋₁ ∈ 𝔭` (for `s = 0` case (b) never occurs).
3. Put `P₀ = B ∩ V(h) = D(f) ∩ V(g₁, ..., gᵣ, h)` and, for `j = 1, ..., s`,
   `Pⱼ = B ∩ D(h) ∩ V(k₁, ..., kⱼ₋₁) ∩ D(kⱼ) = D(f h kⱼ) ∩ V(g₁, ..., gᵣ, k₁, ..., kⱼ₋₁)`; all are
   basic by step 1. Case (a) is `𝔭 ∈ P₀` and case (b) with least index `j` is `𝔭 ∈ Pⱼ`, so
   `B \ C ⊆ P₀ ∪ ... ∪ Pₛ`; conversely each `Pⱼ ⊆ B`, points of `P₀` are outside `D(h) ⊇ C`, and
   points of `Pⱼ` (`j ≥ 1`) are outside `V(k₁, ..., kₛ) ⊇ C`. Hence `B \ C = P₀ ∪ ... ∪ Pₛ`.
4. The pieces are pairwise disjoint: `P₀ ⊆ V(h)` while `Pⱼ ⊆ D(h)` for `j ≥ 1`; for
   `1 ≤ i < j`, `Pᵢ ⊆ D(kᵢ)` while `Pⱼ ⊆ V(kᵢ)`. -/
theorem exists_disjoint_basicConstructibleSetData_diff {A : Type u} [CommRing A]
    (f h : A) (r s : ℕ) (g : Fin r → A) (k : Fin s → A) :
    ∃ (n : ℕ) (S : Fin n → BasicConstructibleSetData A),
      (Pairwise fun i j => Disjoint ((S i).toSet) ((S j).toSet)) ∧
      (⟨f, r, g⟩ : BasicConstructibleSetData A).toSet \
          (⟨h, s, k⟩ : BasicConstructibleSetData A).toSet = ⋃ i, (S i).toSet := by
  sorry

end PrimeSpectrum
