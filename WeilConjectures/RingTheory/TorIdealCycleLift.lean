/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.BigOperators.Fin

/-! # Lifts of cycles in a quotient tensor complex
A degree-one cycle of `P ⊗ R/I`, for a projective resolution `P`, lifts to an element `y` of
`P₁` whose differential is a finite sum of ideal multiples.

## Implementation details

Tensoring a module `E` with `R/I` is identified with `E/IE` by
`TensorProduct.tensorQuotEquivQuotSMul`; no freeness is needed.

## References

* [Stacks, Tag 00M5]
* [Stacks, Tag 00M6]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Every degree-one cycle `z` of `P ⊗ R/I` is of the form `y ⊗ 1` for some `y : P₁`, and
then `d y = ∑ j, a j • p j` for finitely many `a j ∈ I` and `p j : P₀`. -/
theorem exists_quotient_cycle_lift
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M)
    (z : ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).cycles 1) :
    ∃ (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
      ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) ∧
      P.complex.d 1 0 y = ∑ j, (a j : R) • p j := by
  classical
  let C := (((tensoringRight (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e := TensorProduct.tensorQuotEquivQuotSMul (P.complex.X 1) I
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (P.complex.X 1)))
    (e (C.iCycles 1 z))
  have hlift : C.iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) := by
    apply e.injective
    simpa only [Submodule.mkQ_apply, e, ← RingHom.map_one (Ideal.Quotient.mk I),
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul] using hy.symm
  have hzero : (P.complex.d 1 0 y) ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    have h := ConcreteCategory.congr_hom (C.iCycles_d 1 0) z
    change C.d 1 0 (C.iCycles 1 z) = 0 at h
    rw [hlift] at h
    exact h
  have hmem : P.complex.d 1 0 y ∈ I • (⊤ : Submodule R (P.complex.X 0)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := congrArg (TensorProduct.tensorQuotEquivQuotSMul (P.complex.X 0) I) hzero
    simpa only [← RingHom.map_one (Ideal.Quotient.mk I),
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero] using h
  have hfinite : ∀ x ∈ I • (⊤ : Submodule R (P.complex.X 0)),
      ∃ (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        x = ∑ j, (a j : R) • p j := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr p _
      exact ⟨1, fun _ ↦ ⟨r, hr⟩, fun _ ↦ p, by simp⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨k₁, a₁, p₁, h₁⟩ := h₁
      obtain ⟨k₂, a₂, p₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, Fin.addCases a₁ a₂, Fin.addCases p₁ p₂, ?_⟩
      rw [Fin.sum_univ_add]
      simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) h₁ h₂
  obtain ⟨k, a, p, hd⟩ := hfinite _ hmem
  exact ⟨y, k, a, p, hlift, hd⟩

end ModuleCat
