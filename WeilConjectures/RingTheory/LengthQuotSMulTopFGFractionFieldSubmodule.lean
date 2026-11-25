/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.LocalRing.Defs

public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.OrderOfVanishing.Basic
import WeilConjectures.RingTheory.FGFractionFieldSubmoduleLatticePresentation

/-!
# The finite case of the fraction-field quotient length estimate

For a one-dimensional Noetherian local domain `R` and a finitely generated `R`-submodule `M` of
`K^r`, the length of `M/xM` is at most `r · length(R/xR)` for nonzero `x`.

## Implementation details

A lattice presentation gives `M ≃ N ⊆ F = R^s` with `s ≤ r` and `F/N` of finite length. The
exact sequences `0 → F/N → F/xN → F/xF → 0` and `0 → N/xN → F/xN → F/N → 0` give
`length(N/xN) = length(F/xF) = s · length(R/xR)` after cancelling the finite `length(F/N)`; this
replaces the power-of-`x` sandwich of the source.

## References

* [Stacks, Tag 00PE]
-/

@[expose] public section

universe u v

namespace Submodule

open scoped Pointwise

private theorem length_quotSMulTop_eq_of_finite_cokernel
    {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    (N : Submodule R F) (x : R) (hx : Function.Injective (fun m : F ↦ x • m))
    (hN : Module.length R (F ⧸ N) ≠ ⊤) :
    Module.length R (QuotSMulTop x N) = Module.length R (QuotSMulTop x F) := by
  let A : Submodule R F := x • N
  let T : Submodule R F := x • ⊤
  let μ : F →ₗ[R] F := LinearMap.lsmul R F x
  have hcomap : A.comap μ = N := by
    ext m
    change x • m ∈ x • N ↔ m ∈ N
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨n, hn, he⟩ ↦ hx he ▸ hn,
      fun hm ↦ ⟨m, hm, rfl⟩⟩
  have hrange : μ.range = T := by
    ext m
    simp only [LinearMap.mem_range, T, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and]
    rfl
  have hμ : N ≤ A.comap μ := hcomap.ge
  let f := N.mapQ A μ hμ
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  have hAT : A ≤ T := smul_mono_right x le_top
  let g := Submodule.factor hAT
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.range_mapQ, hrange]
    simp
  have hlen₁ := Module.length_eq_add_of_exact f g hf
    (Submodule.factor_surjective hAT) hfg
  have hAN : A ≤ N := by
    rintro m ⟨n, hn, rfl⟩
    exact N.smul_mem x hn
  have hB : A.comap N.subtype = x • (⊤ : Submodule R N) := by
    ext m
    change (m : F) ∈ x • N ↔ m ∈ x • (⊤ : Submodule R N)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨n, hn, he⟩
      exact ⟨⟨n, hn⟩, Subtype.ext he⟩
    · rintro ⟨n, he⟩
      exact ⟨n, n.property, congrArg Subtype.val he⟩
  have hk : x • (⊤ : Submodule R N) ≤ A.comap N.subtype := hB.ge
  let k := (x • (⊤ : Submodule R N)).mapQ A N.subtype hk
  have hki : Function.Injective k := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hB, Submodule.mkQ_map_self]
  let g' := Submodule.factor hAN
  have hkg : Function.Exact k g' := by
    rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.range_mapQ]
    simp
  have hlen₂ := Module.length_eq_add_of_exact k g' hki
    (Submodule.factor_surjective hAN) hkg
  have he : Module.length R (QuotSMulTop x N) + Module.length R (F ⧸ N) =
      Module.length R (QuotSMulTop x F) + Module.length R (F ⧸ N) := by
    rw [← hlen₂, hlen₁, add_comm]
  exact (ENat.add_left_injective_of_ne_top hN) he

private theorem length_quotSMulTop_pi
    {R : Type u} [CommRing R] (s : ℕ) (x : R) :
    Module.length R (QuotSMulTop x (Fin s → R)) =
      (s : ℕ∞) * Module.length R (QuotSMulTop x R) := by
  classical
  have he : x • (⊤ : Submodule R (Fin s → R)) =
      Submodule.pi Set.univ (fun _ : Fin s ↦ x • (⊤ : Submodule R R)) := by
    ext m
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨n, rfl⟩ i
      exact ⟨n i, rfl⟩
    · intro hm
      choose n hn using hm
      exact ⟨n, funext hn⟩
  let e : QuotSMulTop x (Fin s → R) ≃ₗ[R] (Fin s → QuotSMulTop x R) :=
    Submodule.quotEquivOfEq _ _ he ≪≫ₗ Submodule.quotientPi _
  rw [e.length_eq]
  simp

/-- The quotient length bound for a finitely generated fraction-field submodule. -/
theorem length_quotSMulTop_le_of_fg_of_ringKrullDim_eq_one_of_isLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hM : M.FG)
    (hdim : ringKrullDim R = 1) (x : R) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M) ≤
      (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
  classical
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  obtain ⟨s, hsr, N, d, hd, hdN, ⟨e⟩⟩ := exists_lattice_presentation_of_fg r M hM
  have hlen : Module.length R (QuotSMulTop d R) < ⊤ := by
    have hfin := isFiniteLength_quotient_span_singleton R
      (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
    let e' : QuotSMulTop d R ≃ₗ[R] R ⧸ Ideal.span {d} :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [e'.length_eq]
    exact (Module.length_ne_top_iff.mpr hfin).lt_top
  have hN : Module.length R ((Fin s → R) ⧸ N) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (Module.length_le_of_surjective (Submodule.factor hdN)
        (Submodule.factor_surjective hdN))
    rw [length_quotSMulTop_pi]
    exact (WithTop.mul_lt_top (ENat.natCast_lt_top s) hlen).ne
  have hx' : Function.Injective (fun m : Fin s → R ↦ x • m) := by
    intro a b hab
    ext i
    exact mul_left_cancel₀ hx (congrFun hab i)
  rw [(QuotSMulTop.congr x e).length_eq,
    length_quotSMulTop_eq_of_finite_cokernel N x hx' hN, length_quotSMulTop_pi]
  exact mul_le_mul_left (show (s : ℕ∞) ≤ r by exact_mod_cast hsr) _

end Submodule

