/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Augment
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Bounded resolutions by finite projective modules

Source: Stacks Project, Algebra, Tags 00O5 and 0CXE.
(blueprint: lem-weil-pbc-bounded-finite-projective-resolution)
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

private theorem finite_resolution_splice
    {R : Type u} [CommRing R] (n : ℕ)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (hproj : Projective S.X₂)
    (P : ProjectiveResolution S.X₁)
    (hP : ∀ i : ℕ, n < i → IsZero (P.complex.X i))
    (hfin : ∀ i : ℕ, Module.Finite R (P.complex.X i))
    [Module.Finite R S.X₂] :
    ∃ Q : ProjectiveResolution S.X₃,
      (∀ i : ℕ, Module.Finite R (Q.complex.X i)) ∧
      (∀ i : ℕ, n + 1 < i → IsZero (Q.complex.X i)) := by
  let := hS.mono_f
  let := hS.epi_g
  let := hproj
  let a : P.complex.X 0 ⟶ S.X₁ := P.π.f 0
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
  refine ⟨{ complex := K, π := π, quasiIso := hπ, projective := ?_ }, ?_, ?_⟩
  · intro i
    cases i with
    | zero => exact hproj
    | succ i => exact P.projective i
  · intro i
    cases i with
    | zero =>
      change Module.Finite R S.X₂
      infer_instance
    | succ i => exact hfin i
  · intro i hi
    cases i with
    | zero => omega
    | succ i => exact hP i (by omega)

/-- A finite module over a Noetherian ring with projective dimension at most `d`
admits a resolution of length at most `d` by finite projective modules.
Source: Stacks Project, Algebra, Tags 00O5 and 0CXE.
(blueprint: lem-weil-pbc-bounded-finite-projective-resolution)

Proof: Induct on `d`. At zero the module is projective, and its identity resolution
has finite terms. At a successor choose a surjection from a finite free module.
Its kernel is finite by Noetherianity and has projective dimension at most `d`
by dimension shifting. Apply induction to the kernel and splice its resolution
with the chosen surjection. The degree-zero term is the finite free module;
each positive term is the preceding term of the kernel resolution. Thus all
terms remain finite and all terms above `d + 1` vanish. -/
theorem exists_bounded_finite_projective_resolution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (h : HasProjectiveDimensionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, Module.Finite R (P.complex.X i)) ∧
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) := by
  induction d generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr h
    refine ⟨ProjectiveResolution.self M, ?_, ?_⟩
    · intro i
      cases i with
      | zero =>
        change Module.Finite R (((ChainComplex.single₀ _).obj M).X 0)
        rw [ChainComplex.single₀_obj_zero]
        infer_instance
      | succ i =>
        have hz : IsZero ((ProjectiveResolution.self M).complex.X (i + 1)) :=
          HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
        have := ModuleCat.subsingleton_of_isZero hz
        infer_instance
    · intro i hi
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | succ d ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE S.X₁ d :=
      (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp h
    obtain ⟨Q, hQfin, hQzero⟩ := ih S.X₁ hK
    exact finite_resolution_splice d S hS inferInstance Q hQzero hQfin

end ModuleCat
