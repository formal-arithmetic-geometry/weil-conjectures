/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.Augment
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Projective resolutions of bounded length and projective dimension

We show that `ModuleCat.HasProjectiveResolutionLE M n` agrees with Mathlib's
`HasProjectiveDimensionLE M n`, so that Mathlib's projective dimension API applies to
`HasProjectiveResolutionLE`.

Source: Stacks Project, Algebra, Lemmas 065R and 065S
(blueprint: lem-weil-pbc-projective-resolution-ext-degree).
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

/-- Splicing a projective presentation with a resolution of its kernel. -/
private theorem hasProjectiveResolutionLE_of_shortExact_projective_middle
    {R : Type u} [CommRing R] (n : ℕ)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (hproj : Projective S.X₂)
    (hker : HasProjectiveResolutionLE S.X₁ n) :
    HasProjectiveResolutionLE S.X₃ (n + 1) := by
  obtain ⟨P, hP⟩ := hker
  let := hS.mono_f
  let := hS.epi_g
  let := hproj
  let a : P.complex.X 0 ⟶ S.X₁ := P.π.f 0
  have : Epi a := inferInstanceAs (Epi (P.π.f 0))
  have ha : P.complex.d 1 0 ≫ a = 0 := P.complex_d_comp_π_f_zero
  have haf : P.complex.d 1 0 ≫ (a ≫ S.f) = 0 := by rw [← assoc, ha, zero_comp]
  let K := P.complex.augment (a ≫ S.f) haf
  have hw : K.d 1 0 ≫ S.g = 0 := by
    change (a ≫ S.f) ≫ S.g = 0
    rw [assoc, S.zero, comp_zero]
  have hex₀ : (ShortComplex.mk (a ≫ S.f) S.g hw).Exact := by
    let φ : ShortComplex.mk (a ≫ S.f) S.g hw ⟶ S :=
      { τ₁ := a, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS.exact
  have hex₁ : (ShortComplex.mk (P.complex.d 1 0) (a ≫ S.f) haf).Exact := by
    let φ : ShortComplex.mk (P.complex.d 1 0) a ha ⟶
        ShortComplex.mk (P.complex.d 1 0) (a ≫ S.f) haf :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := S.f }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 P.exact₀
  let π := (ChainComplex.toSingle₀Equiv K S.X₃).symm ⟨S.g, hw⟩
  have hπ : QuasiIso π := by
    constructor
    intro i
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk (a ≫ S.f) S.g hw).Exact ∧ Epi S.g
        exact ⟨hex₀, inferInstance⟩
      all_goals rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt' π (i + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i (by simp) (by simp)]
      cases i with
      | zero => exact hex₁
      | succ i => exact P.exact_succ i
  refine ⟨{ complex := K, π := π, quasiIso := hπ, projective := ?_ }, ?_⟩
  · intro i
    cases i with
    | zero => exact hproj
    | succ i => exact P.projective i
  · intro i hi
    cases i with
    | zero => omega
    | succ i => exact hP i (by omega)


/-- A module has a projective resolution of length at most `n` if and only if it has projective
dimension at most `n`, i.e. `Ext^i(M, -)` vanishes for `i > n`.

Source: Stacks Project, Algebra, Lemma 065R
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE M n ↔ HasProjectiveDimensionLE M n := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · rintro ⟨P, hP⟩
    refine HasProjectiveDimensionLT.mk fun i hi Y e ↦ ?_
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) (by omega)
    obtain rfl : f = 0 := (hP i (by omega)).eq_of_src _ _
    exact P.extMk_zero _ _
  · intro h
    induction n generalizing M with
    | zero =>
      have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr h
      exact ⟨ProjectiveResolution.self M, fun i hi ↦
        HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
    | succ n ih =>
      let S := ShortComplex.mk _ _ (kernel.condition (Projective.π M))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π M) }
      have : HasProjectiveDimensionLT S.X₂ (n + 1) :=
        hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
      exact hasProjectiveResolutionLE_of_shortExact_projective_middle n S hS
        (inferInstanceAs (Projective (Projective.over M)))
        (ih _ (hS.hasProjectiveDimensionLT_X₁ (n + 1) this h))

end ModuleCat
