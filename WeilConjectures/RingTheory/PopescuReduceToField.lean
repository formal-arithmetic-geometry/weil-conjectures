/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.DesingularizeStrictlyStandard
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.PopescuFinalSolve
import WeilConjectures.RingTheory.PopescuMaximalBadQuotient
import WeilConjectures.Algebra.PopescuLiftNilpotent
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.PopescuStandardNonzerodivisor
import WeilConjectures.RingTheory.PopescuSmoothLiftModuloEight

/-!
# Popescu's theorem reduces to a field as base

If Popescu's theorem holds for regular maps from fields, it holds for regular maps between
arbitrary Noetherian rings.

## Implementation details

Fields and source rings live in universe `u`; target rings, algebras and index categories live
in `max u v`, as in the other Popescu reduction steps (lifting along a nilpotent ideal and
finite products): the proof applies the hypothesis to the residue fields `K_i` of `R`
(universe `u`) and the fibre rings `Λ ⊗_R K_i` (universe `max u v`).

## References

* [Stacks, Tag 07F5]
-/

@[expose] public section

universe u v

open CategoryTheory

/-- Assume that for every field `k` and every Noetherian ring `Λ` with a regular ring map
`k → Λ`, `Λ` is a filtered colimit of smooth `k`-algebras. Then for all Noetherian rings
`R`, `Λ` and every regular ring map `R → Λ`, `Λ` is a filtered colimit of smooth
`R`-algebras. -/
theorem popescu_reduce_to_field
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ)) :
    ∀ (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
      [IsNoetherianRing R] [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap R Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} R ↦ Algebra.Smooth R B)
          (CommAlgCat.of R Λ) := by
  classical
  intro R Λ _ _ _ _ _ hreg
  by_contra hbad
  obtain ⟨R', Λ', _, _, _, _, _, _, hreg', hbad', hquot⟩ :=
    exists_popescu_maximal_bad_quotient R Λ hreg hbad
  have hred : IsReduced R' := by
    apply nilradical_eq_bot_iff.mp
    by_contra hN
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical R'
    have hnpos : 1 ≤ n := by
      by_contra hnpos
      have hnzero : n = 0 := by omega
      simp [hnzero] at hn
    apply hbad'
    exact Algebra.popescu_lift_nilpotent R' Λ' (nilradical R')
      ⟨n, hnpos, hn⟩ (hquot _ hN) hreg'.1
  let : IsReduced R' := hred
  apply hbad'
  obtain ⟨J, _, _, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization R' (CommAlgCat.of R' Λ')
      {B | Algebra.Smooth R' B}
      (fun B hB ↦ by
        let : Algebra.Smooth R' B := hB
        infer_instance) (fun A hA α ↦ by
          let : Algebra.FinitePresentation R' A := hA
          obtain ⟨A₀, _, _, _, a₀, α₀, π, hcomp₀, hπ, hstandard⟩ :=
            exists_popescu_standard_nonzerodivisor h R' Λ' hreg' A α.hom
          let : Module.Flat R' Λ' := RingHom.flat_algebraMap_iff.mp hreg'.1
          have hπΛ : algebraMap R' Λ' π ∈ nonZeroDivisors Λ' := by
            rw [mem_nonZeroDivisors_iff_left]
            intro l hl
            have hinj := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Λ') hπ
            apply hinj
            simpa [Algebra.smul_def] using hl
          have hI : Ideal.span {π ^ 8} ≠ (⊥ : Ideal R') := by
            intro hI
            have hz : π ^ 8 = 0 := by
              have hmem := Ideal.subset_span (Set.mem_singleton (π ^ 8))
              rw [hI] at hmem
              exact Ideal.mem_bot.mp hmem
            exact nonZeroDivisors.ne_zero ((nonZeroDivisors R').pow_mem hπ 8) hz
          obtain ⟨D₀, _, _, _, δ, hsing, hmod⟩ :=
            exists_popescu_smooth_lift_modulo_eight R' Λ' A₀ α₀ π hπ hπΛ (hquot _ hI)
          have hR : ∀ r : R', r * π = 0 ↔ r * π ^ 2 = 0 := by
            intro r
            rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hπ,
              mul_right_mem_nonZeroDivisors_eq_zero_iff ((nonZeroDivisors R').pow_mem hπ 2)]
          have hΛ : ∀ l : Λ', l * algebraMap R' Λ' π = 0 ↔
              l * (algebraMap R' Λ' π) ^ 2 = 0 := by
            intro l
            rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hπΛ,
              mul_right_mem_nonZeroDivisors_eq_zero_iff ((nonZeroDivisors Λ').pow_mem hπΛ 2)]
          obtain ⟨B, _, _, hBfp, β, aB, dB, hcomp, _, _, hle⟩ :=
            Algebra.exists_desingularization_strictlyStandard
              R' Λ' A₀ D₀ π α₀ δ hR hΛ hstandard hmod
          let : Algebra.FinitePresentation R' B := hBfp
          have hsingB : Algebra.singularIdeal R' B = ⊤ := by
            apply top_unique
            rw [hsing] at hle
            rw [Ideal.map_top] at hle
            exact hle
          have hmap : Ideal.map β.toRingHom (Algebra.singularIdeal R' B) = ⊤ := by
            rw [hsingB, Ideal.map_top]
          obtain ⟨C, _, _, hC, bC, γ, hcompC⟩ :=
            Algebra.exists_smooth_factorization_of_singularIdeal_map_eq_top β hmap
          refine ⟨CommAlgCat.of R' C, hC,
            CommAlgCat.ofHom (bC.comp (aB.comp a₀)), CommAlgCat.ofHom γ, ?_⟩
          apply CommAlgCat.hom_ext
          change γ.comp (bC.comp (aB.comp a₀)) = α.hom
          rw [← AlgHom.comp_assoc, hcompC, ← AlgHom.comp_assoc, hcomp, hcomp₀])
  exact ⟨J, inferInstance, inferInstance, ⟨D, ι, hc⟩, hD⟩
