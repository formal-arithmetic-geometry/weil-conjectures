/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Completeness for subideals of the maximal ideal

A complete Noetherian local ring is complete for every ideal contained in its maximal ideal.

## Implementation details

An `I`-adic Cauchy sequence is adic Cauchy for the maximal ideal, hence has a limit `L`. The
Krull intersection theorem in the finite modules `R ⧸ I^n` shows that the sequence converges
`I`-adically to `L`; Krull intersection for `I` gives separatedness.

## References

* [Stacks, Tag 00IP] (Krull intersection)
* [Stacks, Tag 0317] (completeness)
-/

@[expose] public section

universe u

/-- A complete Noetherian local ring is complete for every subideal of its
maximal ideal. -/
theorem IsAdicComplete.of_le_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) : IsAdicComplete I R := by
  have : IsHausdorff I R :=
    IsHausdorff.of_le_jacobson I R (hI.trans (IsLocalRing.maximalIdeal_le_jacobson _))
  refine { prec' := ?_ }
  intro f hf
  obtain ⟨L, hL⟩ := IsPrecomplete.prec'
    (I := IsLocalRing.maximalIdeal R) (M := R) f (fun {m n} hmn ↦
      SModEq.mono (Submodule.smul_mono_left (pow_le_pow_left' hI m)) (hf hmn))
  refine ⟨L, fun n ↦ SModEq.sub_mem.mpr ?_⟩
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  let Q := R ⧸ (I ^ n : Submodule R R)
  let q : R →ₗ[R] Q := (I ^ n : Submodule R R).mkQ
  have hz : q (f n - L) = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal R)
    intro k
    let t := max n k
    have hnt : f n - f t ∈ I ^ n := by
      simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using
        hf (show n ≤ t from le_max_left _ _)
    have hqt : q (f n - f t) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hnt
    have hdiff : q (f n - L) = q (f t - L) := by
      have heq : f n - L = (f n - f t) + (f t - L) := by abel
      rw [heq, map_add, hqt, zero_add]
    rw [hdiff]
    apply SModEq.zero.mpr
    have hm : f t - L ∈
        (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R R) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n k)))
        (SModEq.sub_mem.mp (hL t))
    exact Submodule.smul_top_le_comap_smul_top _ q hm
  exact (Submodule.Quotient.mk_eq_zero _).mp hz
