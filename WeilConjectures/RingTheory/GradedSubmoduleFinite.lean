/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite homogeneous generators for graded submodules over the projective-line ring

A homogeneous submodule of a finitely generated graded `k[x₀,x₁]`-module is spanned by finitely
many homogeneous elements (`MvPolynomial.graded_submodule_finite`).

## Implementation details

The module grading is an internal direct sum `ℳ` of additive subgroups indexed by `ℤ`; the
polynomial ring has its total-degree grading. Gradedness of the submodule is Mathlib's
`Submodule.IsHomogeneous` for the decomposition `hℳ.chooseDecomposition` (which is unique, so the
choice is immaterial). The proof uses that `k[x₀,x₁]` is Noetherian and replaces a finite
generating set of the submodule by the homogeneous components of its elements.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A graded submodule of a finite graded module over `k[x₀,x₁]` has finite homogeneous
generators. -/
theorem graded_submodule_finite {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → f • x ∈ ℳ ((n : ℤ) + j))
    (hN : ∃ s : Set N, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (K : Submodule (MvPolynomial (Fin 2) k) N)
    (hK : letI : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition; K.IsHomogeneous ℳ) :
    ∃ s : Set N, s.Finite ∧ (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = K := by
  classical
  have _hsmul := hsmul
  let : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  obtain ⟨sN, hsN, _, hspanN⟩ := hN
  let : Module.Finite (MvPolynomial (Fin 2) k) N :=
    Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨sN, hsN, hspanN⟩)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian K
  let t : Finset N := s.biUnion fun x ↦
    (DirectSum.decompose ℳ x).support.image fun i ↦ (DirectSum.decompose ℳ x i : N)
  have ht : ∀ y ∈ t, ∃ x ∈ s, ∃ i : ℤ, y = (DirectSum.decompose ℳ x i : N) := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx, i, rfl⟩
  refine ⟨(t : Set N), t.finite_toSet, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, i, rfl⟩ := ht y hy
    exact ⟨i, (DirectSum.decompose ℳ x i).property⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨x, hx, i, rfl⟩ := ht y hy
      exact (hK.mem_iff ℳ).mp (hs ▸ Submodule.subset_span hx) i
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro x hx
      rw [← DirectSum.sum_support_decompose ℳ x]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.subset_span
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

end MvPolynomial
