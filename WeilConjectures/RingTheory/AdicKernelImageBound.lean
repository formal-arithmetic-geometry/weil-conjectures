/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Filtration

/-! # Artin--Rees bound for images of reduced kernels

We show, using the Artin--Rees lemma, that for a linear map `f : M → N` with `N` finite over a
Noetherian ring, the elements of `M / I^(m+1) M` coming from `f⁻¹(I^(l+1) N)` are exactly
those coming from `ker f`, once `l ≥ m + c` for a constant `c`.

## References

* Stacks Project, Lemma 087X, proof of claim (a); Lemma 00IN.
-/

@[expose] public section

universe u v w

namespace LinearMap

/-- Let `R` be Noetherian, `N` a finite `R`-module, `f : M → N` linear and `I` an ideal. There is
`c` such that for all `m + c ≤ l`, the image of `f⁻¹(I^(l+1) N)` in `M / I^(m+1) M` equals the
image of `ker f`. -/
theorem adic_kernel_image_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ (l m : ℕ), m + c ≤ l →
      ((I ^ (l + 1) • (⊤ : Submodule R N)).comap f).map
          (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ =
        f.ker.map (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul f.range
  refine ⟨c, fun l m h ↦ ?_⟩
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    have hx' : f x ∈ I ^ (l + 1) • (⊤ : Submodule R N) ⊓ f.range :=
      ⟨hx, ⟨x, rfl⟩⟩
    rw [hc (l + 1) (by omega)] at hx'
    have hy' : f x ∈ (I ^ (l + 1 - c) • (⊤ : Submodule R M)).map f := by
      rw [Submodule.map_smul'', Submodule.map_top]
      have hle : I ^ (l + 1 - c) •
          (I ^ c • (⊤ : Submodule R N) ⊓ f.range) ≤ I ^ (l + 1 - c) • f.range :=
        smul_mono_right _ inf_le_right
      exact hle hx'
    obtain ⟨y, hy, hfy⟩ := hy'
    have hym : y ∈ I ^ (m + 1) • (⊤ : Submodule R M) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hy
    refine ⟨x - y, ?_, ?_⟩
    · change f (x - y) = 0
      rw [map_sub, hfy, sub_self]
    · rw [map_sub]
      have hy0 : (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ y = 0 := by
        exact (Submodule.Quotient.mk_eq_zero _).mpr hym
      rw [hy0, sub_zero]
  · apply Submodule.map_mono
    intro x hx
    change f x ∈ I ^ (l + 1) • (⊤ : Submodule R N)
    rw [LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _

end LinearMap
