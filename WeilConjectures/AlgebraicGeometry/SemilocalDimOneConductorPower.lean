/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.IntegralOverringJacobsonPower
import WeilConjectures.RingTheory.FiniteIntegralConductor
import WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPowerAux
import WeilConjectures.AlgebraicGeometry.FiniteConductorMul

/-! # Conductor powers in a semilocal normalization

## References

* [Stacks Project, Tag 09N2](https://stacks.math.columbia.edu/tag/09N2)
-/

@[expose] public section
universe u v

/-- Conductor-power conclusion for the normalization in Varieties Lemma 09N2.
-/
theorem semilocal_dim_one_conductor_power
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]
    [Finite (MaximalSpectrum (integralClosure B K))] :
    ∀ x y : integralClosure B K,
      x ≠ 0 → x ∈ Ideal.jacobson (⊥ : Ideal (integralClosure B K)) →
        ∃ n : ℕ, 0 < n ∧ ∃ b : B,
          algebraMap B K b = (x : K) ^ n * (y : K) := by
  intro x y hx hJ
  obtain ⟨A, hfin, hfrac, hxm, hym, m, hm, a, haK, haJ⟩ :=
    exists_finite_adjoin_with_jacobson_power B K x y hJ
  set_option linter.style.haveILetI false in
    letI : Module.Finite B A := hfin
  set_option linter.style.haveILetI false in
    letI : IsFractionRing A K := hfrac
  obtain ⟨r, hr, hconductor⟩ := Subalgebra.exists_jacobson_pow_mul_mem_base hdim A
  have hpow : a ^ r ∈
      (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))) ^ r :=
    Ideal.pow_mem_pow haJ r
  obtain ⟨b, hb⟩ := Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
    hdim A hconductor (a ^ r) hpow ⟨(y : K), hym⟩
  refine ⟨m * r, Nat.mul_pos hm hr, b, ?_⟩
  calc
    algebraMap B K b = (a : K) ^ r * (y : K) := hb
    _ = ((x : K) ^ m) ^ r * (y : K) := by rw [haK]
    _ = (x : K) ^ (m * r) * (y : K) := by rw [pow_mul]
