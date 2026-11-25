/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.Algebra.Exact.Basic

/-!
# Associated primes in a short exact sequence over an arbitrary ring

For a short exact sequence `0 → M' → M → M'' → 0`, we have
`Ass(M') ⊆ Ass(M) ⊆ Ass(M') ∪ Ass(M'')`, where associated primes are defined via element
annihilators.

## Implementation details

The surjectivity hypothesis on `g` is not used in the proof; it is kept as part of short
exactness.

## References

* Stacks Project, Algebra, Lemma 02M3, first two assertions.
-/

@[expose] public section

universe uR uSub uMid uQuot

namespace RingTheory

/-- Let `f : M' → M` and `g : M → M''` form a short exact sequence of modules over a
commutative ring. Then `f` preserves element annihilators, every associated prime of `M'` is
associated to `M`, and every associated prime of `M` is associated to `M'` or to `M''`. No
Noetherian hypothesis is needed. -/
theorem annihilatorAssociatedPrimes_of_shortExact
    {R : Type uR} [CommRing R]
    {M' : Type uSub} [AddCommGroup M'] [Module R M']
    {M : Type uMid} [AddCommGroup M] [Module R M]
    {M'' : Type uQuot} [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    (annihilatorAssociatedPrimes R M' ⊆ annihilatorAssociatedPrimes R M) ∧
    (∀ z' : M', (⊥ : Submodule R M).colon {f z'} =
      (⊥ : Submodule R M').colon {z'}) ∧
    (annihilatorAssociatedPrimes R M ⊆
      annihilatorAssociatedPrimes R M' ∪ annihilatorAssociatedPrimes R M'') := by
  classical
  have _ := hg
  have hann (z' : M') : (⊥ : Submodule R M).colon {f z'} =
      (⊥ : Submodule R M').colon {z'} := by
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← map_smul, map_eq_zero_iff f hf]
  refine ⟨?_, hann, ?_⟩
  · rintro q ⟨hq, z', hz'⟩
    exact ⟨hq, f z', hz'.trans (hann z').symm⟩
  · rintro q ⟨hq, z, hz⟩
    have hmem (a : R) : a ∈ q ↔ a • z = 0 := by
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot]
    by_cases h : ∃ s : R, s ∉ q ∧ ∃ z' : M', f z' = s • z
    · obtain ⟨s, hs, z', hz'⟩ := h
      left
      refine ⟨hq, z', ?_⟩
      rw [← hann z', hz']
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← mul_smul]
      rw [← hmem]
      exact ⟨fun ha ↦ q.mul_mem_right s ha,
        fun has ↦ (hq.mem_or_mem has).resolve_right hs⟩
    · right
      refine ⟨hq, g z, ?_⟩
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      constructor
      · intro ha
        rw [← map_smul, (hmem a).mp ha, map_zero]
      · intro ha
        by_contra haq
        apply h
        refine ⟨a, haq, ?_⟩
        have hker : a • z ∈ LinearMap.ker g := by
          rw [LinearMap.mem_ker, map_smul, ha]
        rw [hfg.linearMap_ker_eq] at hker
        exact hker

end RingTheory
