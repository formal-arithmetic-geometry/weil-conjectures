/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusEmbeddingSpectralBounds
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Upper weights descend through a quotient and a positive Frobenius power

Source: latest blueprint, sk-thm-wft-affine-curve-upper, final paragraph.
(blueprint: lem-a1-embedding-power-quotient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v

namespace FrobeniusModule

/-- Suppose a finite Frobenius module with upper bound w relative to q^m surjects onto
V, intertwining its Frobenius with T^m, where m is positive. Then V is finite dimensional,
T is invertible, and its mixed upper bound relative to q is w.

Source: latest blueprint, sk-thm-wft-affine-curve-upper, final paragraph: quotient
stability and reflection after the finite constant extension.
(blueprint: lem-a1-embedding-power-quotient).

Proof: the surjection gives finite dimensionality of V. Surjectivity of the source
Frobenius implies surjectivity of T^m and hence of T. On the finite-dimensional target
this makes T an automorphism. An eigenvalue alpha of T gives alpha^m for T^m, hence
for the source. Its bound is |iota(alpha)|^m <= (q^(w/2))^m. Taking the positive m-th
root gives the desired spectral bound. The spectral-filtration equivalence gives the
mixed filtration; the zero-dimensional case is included. -/
theorem mixed_of_power_quotient
    {K : Type v} [Field K] [IsAlgClosed K]
    (iota : K →+* ℂ) (q m : ℕ) (hq : 1 < q) (hm : 1 ≤ m)
    {V : Type u} [AddCommGroup V] [Module K V]
    (T : Module.End K V) (M : FrobeniusModule.{u, v} K)
    (f : M.carrier →ₗ[K] V) (hf : Function.Surjective f)
    (heq : ∀ x, f (M.frobenius x) = (T ^ m) (f x))
    (w : ℝ) (hM : IsMixedOfWeightsAtMostEmbedding iota (q ^ m) M w) :
    ∃ (hfin : FiniteDimensional K V) (G : V ≃ₗ[K] V),
      G.toLinearMap = T ∧ IsMixedOfWeightsAtMostEmbedding iota q
        { carrier := V, finiteDimensional := hfin, frobenius := G } w := by
  classical
  let hfin : FiniteDimensional K V := FiniteDimensional.of_surjective f hf
  have hpow : Function.Surjective (T ^ m) := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    refine ⟨f (M.frobenius.symm x), ?_⟩
    exact (heq (M.frobenius.symm x)).symm.trans
      (congrArg f (M.frobenius.apply_symm_apply x))
  have hT : Function.Surjective T := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    intro y
    obtain ⟨x, hx⟩ := hpow y
    refine ⟨(T ^ n) x, ?_⟩
    simpa only [pow_succ', Module.End.mul_apply] using hx
  let G : V ≃ₗ[K] V := LinearEquiv.ofBijective T
    ⟨LinearMap.injective_iff_surjective.mpr hT, hT⟩
  refine ⟨hfin, G, rfl, ?_⟩
  apply (isMixedOfWeightsAtMostEmbedding_iff_hasWeightsAtMost iota q hq _ w).mpr
  have hqm : 1 < q ^ m := one_lt_pow₀ hq (by omega)
  have hMb := (isMixedOfWeightsAtMostEmbedding_iff_hasWeightsAtMost
    iota (q ^ m) hqm M w).mp hM
  intro α hα
  change T.HasEigenvalue α at hα
  have hαm := hα.pow m
  have hαM := Module.End.hasEigenvalue_of_comp_eq_comp M.frobeniusEnd (T ^ m) f hf
    (by ext x; exact heq x) hαm
  have hb := hMb (α ^ m) hαM
  rw [map_pow, norm_pow, Nat.cast_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg q)] at hb
  exact le_of_pow_le_pow_left₀ (by omega) (Real.rpow_nonneg (Nat.cast_nonneg q) _) hb

end FrobeniusModule
