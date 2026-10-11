/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Basis, inclusions and finite coverings of standard opens of Proj

Source: Stacks Project, Constructions, Section 01M3 and Lemma 01M4;
Algebra, Lemma 00JP (blueprint: lem-weil-pbc-proj-standard-open-inclusion).
-/

universe u v w

namespace AlgebraicGeometry.Proj

/-- Standard opens of positive homogeneous degree form a basis, intersect by multiplication,
and satisfy the power-divisibility inclusion and degree-zero unit-ideal covering criteria.
Source: Stacks Project, Constructions, Section 01M3 and Lemma 01M4 (1)(a),(b), (2), (3);
Algebra, Lemma 00JP (blueprint: lem-weil-pbc-proj-standard-open-inclusion).

Proof:
1. By `lem-weil-pbc-projective-spectrum-basic-opens-basis`, basic opens are open and
   `D(fg) = D(f) ∩ D(g)` because each point represents a prime ideal.
2. Decompose an element defining a basic neighbourhood into homogeneous components.
   A component outside the point's prime gives a smaller neighbourhood; if its degree
   is zero, multiply it by a positive-degree homogeneous element outside that prime.
   Such an element exists because the prime does not contain the irrelevant ideal.
3. For `D₊(g) ⊆ D₊(f)`, the chart identification from
   `lem-weil-pbc-proj-basic-open-intersection` identifies the inverse image of `D₊(f)`
   with the principal open of `f ^ deg g / g ^ deg f`. It is the whole spectrum, so
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` makes this fraction a unit.
4. It follows that `f` is invertible in `S_g`. Write its inverse as `b / g ^ n`, enlarge
   `n` to be positive with `n * deg g ≥ deg f`, and clear a power of `g` from the
   localization equality. Taking the appropriate homogeneous component of `b` gives
   `g ^ e = a * f`, with `a` homogeneous and `e ≥ 1`. If the product is nonzero,
   comparison of homogeneous degrees gives `deg a = e * deg g - deg f`.
5. Conversely, such a relation shows that any prime avoiding `g` avoids `f`.
   The inverse of `f` is `a / g ^ e`; the inverse of the degree-zero fraction is
   `a ^ deg g / g ^ (e * deg g - deg f)`. If `a * f = 0`, `g` is nilpotent,
   both localizations are zero rings, and the unit assertions still hold.
6. The chart is homeomorphic to the spectrum of the degree-zero localization, hence
   quasi-compact by `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.
   Refine an arbitrary open cover using step 2, then take a finite subcover.
7. The chart pulls back the opens `D₊(gᵢ)` to principal opens of
   `gᵢ ^ deg f / f ^ deg gᵢ`. By the same spectrum lemma, these cover the chart
   exactly when their generators span the unit ideal.
-/
theorem standardOpenProperties
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    TopologicalSpace.Opens.IsBasis
      {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} ∧
    (∀ (f g : S) (d k : ℕ), 0 < d → 0 < k → f ∈ 𝒜 d → g ∈ 𝒜 k →
      basicOpen 𝒜 f ⊓ basicOpen 𝒜 g = basicOpen 𝒜 (f * g)) ∧
    (∀ (f g : S) (d k : ℕ) (_hd : 0 < d) (_hk : 0 < k)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k),
      (basicOpen 𝒜 g ≤ basicOpen 𝒜 f ↔
        ∃ (e l : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 l ∧ g ^ e = a * f) ∧
      (∀ (e l : ℕ) (a : S), 0 < e → a ∈ 𝒜 l → g ^ e = a * f →
        a * f ≠ 0 → l = e * k - d) ∧
      (basicOpen 𝒜 g ≤ basicOpen 𝒜 f →
        IsUnit (algebraMap S (Localization.Away g) f) ∧
        IsUnit (HomogeneousLocalization.Away.mk 𝒜 hg d (f ^ k)
          (by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded k hf)))) ∧
    (∀ (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      ∀ (I : Type w) (U : I → (Proj 𝒜).Opens),
        (⨆ i, U i) = basicOpen 𝒜 f →
        ∃ (n : ℕ) (g : Fin n → S) (k : Fin n → ℕ),
          (∀ i, 0 < k i ∧ g i ∈ 𝒜 (k i)) ∧
          basicOpen 𝒜 f = ⨆ i, basicOpen 𝒜 (g i) ∧
          ∀ i, ∃ j, basicOpen 𝒜 (g i) ≤ U j) ∧
    (∀ (f : S) (d : ℕ) (_hd : 0 < d) (hf : f ∈ 𝒜 d)
      (n : ℕ) (g : Fin n → S) (k : Fin n → ℕ)
      (_hk : ∀ i, 0 < k i) (hg : ∀ i, g i ∈ 𝒜 (k i)),
      basicOpen 𝒜 f ≤ ⨆ i, basicOpen 𝒜 (g i) ↔
        Ideal.span (Set.range (fun i : Fin n ↦
          HomogeneousLocalization.Away.mk 𝒜 hf (k i) (g i ^ d)
            (by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d (hg i)))) = ⊤) := by
  sorry

end AlgebraicGeometry.Proj
