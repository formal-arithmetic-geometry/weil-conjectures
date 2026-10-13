/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.Augment

/-!
# Projective dimension and bounded projective resolutions

Mathlib's Ext-vanishing dimension predicate is equivalent to the existence of an
actual projective resolution supported in degrees at most the given bound.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3).
-/

@[expose] public section

universe u v

open CategoryTheory
namespace ModuleCat

/-- In an abelian category with enough projectives, an object has a projective resolution
supported in degrees at most `n` precisely when its projective dimension is at most `n`.

Proof: represent Ext classes by cocycles on a bounded resolution. Above the bound,
the source of each cocycle is zero, so Mathlib's projective dimension criterion applies.
Conversely, induct on `n`. At zero use the identity resolution of a projective object.
At a successor take the kernel of a projective epimorphism, use Mathlib's dimension
shifting to apply induction to that kernel, then augment its resolution by the
projective middle term. Exactness in degrees zero and one follows from the kernel
sequence; higher exactness and the support bound follow from the shorter resolution.
This constructs the complex and augmentation, rather than restating Ext vanishing.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3); the proof uses only the
abelian-category axioms and enough projectives.
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem projective_resolution_ext_degree
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    (X : C) (n : ℕ) :
    (∃ P : ProjectiveResolution X, ∀ i : ℕ, n < i → Limits.IsZero (P.complex.X i)) ↔
      HasProjectiveDimensionLE X n := by
  let := HasExt.standard C
  constructor
  · rintro ⟨P, hP⟩
    apply HasProjectiveDimensionLT.mk
    intro i hi Y a
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (i + 1) (by omega)
    have hfzero : f = 0 := (hP i (by omega)).eq_of_src _ _
    subst f
    exact P.extMk_zero _ _
  · intro h
    induction n generalizing X with
    | zero =>
      have : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr h
      refine ⟨ProjectiveResolution.self X, fun i hi ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    | succ n ih =>
      let S := ShortComplex.mk _ _ (Limits.kernel.condition (Projective.π X))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hK : HasProjectiveDimensionLE S.X₁ n :=
        (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
      obtain ⟨Q, hQ⟩ := ih S.X₁ hK
      have := hS.mono_f
      have := hS.epi_g
      let δ := Q.π.f 0 ≫ S.f
      have w : Q.complex.d 1 0 ≫ δ = 0 := by
        simp [δ, ← Category.assoc]
      let K := Q.complex.augment δ w
      have hδ : K.d 1 0 ≫ S.g = 0 := by
        simp [K, δ, Category.assoc]
      let π := (ChainComplex.toSingle₀Equiv K S.X₃).symm ⟨S.g, hδ⟩
      have hzero : (ShortComplex.mk δ S.g hδ).Exact := by
        let φ : ShortComplex.mk δ S.g hδ ⟶ S :=
          { τ₁ := Q.π.f 0, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS.exact
      have hone : (ShortComplex.mk (Q.complex.d 1 0) δ w).Exact := by
        let φ : ShortComplex.mk _ _ Q.complex_d_comp_π_f_zero ⟶
            ShortComplex.mk (Q.complex.d 1 0) δ w :=
          { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := S.f }
        apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
        exact ShortComplex.exact_of_g_is_cokernel _ Q.isColimitCokernelCofork
      have hπ : QuasiIso π := ⟨fun i ↦ by
        cases i with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · dsimp [HomologicalComplex.shortComplexFunctor', HomologicalComplex.sc']
            simp only [π, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
            change (ShortComplex.mk δ S.g hδ).Exact ∧ Epi S.g
            exact ⟨hzero, inferInstance⟩
          all_goals rfl
        | succ i =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i
              (by simp) (by simp)]
            cases i with
            | zero => exact hone
            | succ i => simpa [K, HomologicalComplex.sc',
                HomologicalComplex.shortComplexFunctor'] using Q.exact_succ i
          · apply ChainComplex.exactAt_succ_single_obj⟩
      let P : ProjectiveResolution S.X₃ :=
        { complex := K
          projective := fun i ↦ by
            cases i with
            | zero => exact inferInstanceAs (Projective S.X₂)
            | succ i => exact Q.projective i
          π := π
          quasiIso := hπ }
      refine ⟨P, fun i hi ↦ ?_⟩
      cases i with
      | zero => omega
      | succ i => exact hQ i (by omega)

end ModuleCat
