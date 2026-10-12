/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Pseudoelements

/-!
# Pulling back a short exact sequence

For a short complex `S : X₁ ⟶ X₂ ⟶ X₃` in an abelian category and `φ : Y ⟶ X₃`, the short
complex `X₁ ⟶ X₂ ×_{X₃} Y ⟶ Y` (`CategoryTheory.ShortComplex.pullback`) is short exact when `S`
is (`CategoryTheory.ShortComplex.ShortExact.pullback`), and comes with a morphism to `S`
(`CategoryTheory.ShortComplex.pullbackHom`) which is the identity on `X₁`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) {Y : C} (φ : Y ⟶ S.X₃)

/-- The pullback `X₁ ⟶ X₂ ×_{X₃} Y ⟶ Y` of a short complex `X₁ ⟶ X₂ ⟶ X₃` along `φ : Y ⟶ X₃`. -/
noncomputable def pullback : ShortComplex C :=
  ShortComplex.mk (pullback.lift S.f 0 (by simp)) (pullback.snd S.g φ) (by simp)

/-- The morphism from the pullback of a short complex to the short complex. -/
@[simps]
noncomputable def pullbackHom : S.pullback φ ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst _ _
  τ₃ := φ
  comm₁₂ := by simp [ShortComplex.pullback]
  comm₂₃ := pullback.condition

variable {S}

/-- The pullback of a short exact sequence is short exact. -/
lemma ShortExact.pullback (hS : S.ShortExact) : (S.pullback φ).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have : Mono (S.pullback φ).f := by
    have h : (S.pullback φ).f ≫ Limits.pullback.fst S.g φ = S.f := Limits.pullback.lift_fst _ _ _
    exact mono_of_mono_fac h
  refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_
           epi_g := inferInstanceAs (Epi (Limits.pullback.snd S.g φ)) }
  refine KernelFork.IsLimit.ofι _ _ (fun {W} t ht ↦ hS.exact.lift (t ≫ Limits.pullback.fst _ _)
      (by
        have ht' : t ≫ Limits.pullback.snd S.g φ = 0 := ht
        rw [Category.assoc, Limits.pullback.condition, reassoc_of% ht', zero_comp]))
    (fun {W} t ht ↦ ?_) (fun {W} t ht m hm ↦ ?_)
  · apply Limits.pullback.hom_ext
    · simp [ShortComplex.pullback]
    · simp only [ShortComplex.pullback, Category.assoc, Limits.pullback.lift_snd, comp_zero]
      exact ht.symm
  · rw [← cancel_mono (S.pullback φ).f, hm]
    apply Limits.pullback.hom_ext
    · simp [ShortComplex.pullback]
    · simp only [ShortComplex.pullback, Category.assoc, Limits.pullback.lift_snd, comp_zero]
      exact ht

variable (S) in
/-- For `ψ : Y' ⟶ Y` and `φ : Y ⟶ X₃`, the morphism from the pullback of a short complex along
`ψ ≫ φ` to its pullback along `φ`, which is the identity on `X₁`. -/
@[simps]
noncomputable def pullbackMap {Y' : C} (ψ : Y' ⟶ Y) : S.pullback (ψ ≫ φ) ⟶ S.pullback φ where
  τ₁ := 𝟙 _
  τ₂ := Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ ψ)
    (by rw [Limits.pullback.condition, Category.assoc])
  τ₃ := ψ
  comm₁₂ := by
    apply Limits.pullback.hom_ext <;> simp [ShortComplex.pullback]
  comm₂₃ := by simp [ShortComplex.pullback]

end CategoryTheory.ShortComplex
