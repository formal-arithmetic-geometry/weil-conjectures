/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The short exact sequence cut out of a five-term exact sequence

Given an exact sequence `X₁ ⟶ X₂ ⟶ L ⟶ Y₁ ⟶ Y₂` in an abelian category, the induced
sequence `0 ⟶ coker (X₁ ⟶ X₂) ⟶ L ⟶ ker (Y₁ ⟶ Y₂) ⟶ 0` is short exact. Here the kernel
is any limit kernel fork of `Y₁ ⟶ Y₂`.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [Abelian C]

/-- In an exact sequence `X₁ ⟶ X₂ ⟶ L ⟶ Y₁ ⟶ Y₂` of an abelian category, the cokernel
of `X₁ ⟶ X₂`, the object `L` and a kernel `Z` of `Y₁ ⟶ Y₂` form a short exact sequence. -/
lemma shortExact_cokernelDesc_of_exact {X₁ X₂ L Y₁ Y₂ Z : C} {u : X₁ ⟶ X₂} {d : X₂ ⟶ L}
    {v : L ⟶ Y₁} {w : Y₁ ⟶ Y₂} (hud : u ≫ d = 0) (hdv : d ≫ v = 0) (hvw : v ≫ w = 0)
    (h₁ : (ShortComplex.mk u d hud).Exact) (h₂ : (ShortComplex.mk d v hdv).Exact)
    (h₃ : (ShortComplex.mk v w hvw).Exact) {j : Z ⟶ Y₁} {hjw : j ≫ w = 0}
    (hj : IsLimit (KernelFork.ofι j hjw)) (b : L ⟶ Z) (hb : b ≫ j = v) :
    ∃ h : cokernel.desc u d hud ≫ b = 0,
      (ShortComplex.mk (cokernel.desc u d hud) b h).ShortExact := by
  have : Mono j := mono_of_isLimit_fork hj
  have h : cokernel.desc u d hud ≫ b = 0 := by
    rw [← cancel_mono j, assoc, hb, zero_comp]
    exact coequalizer.hom_ext (by simpa using hdv)
  refine ⟨h, ?_⟩
  have : Mono (cokernel.desc u d hud) := h₁.mono_cokernelDesc
  let e := IsLimit.conePointUniqueUpToIso hj (kernelIsKernel w)
  have he : e.hom ≫ kernel.ι w = j :=
    IsLimit.conePointUniqueUpToIso_hom_comp hj (kernelIsKernel w) WalkingParallelPair.zero
  have : Epi (kernel.lift w v hvw) := h₃.epi_kernelLift
  have hbe : b ≫ e.hom = kernel.lift w v hvw := by
    rw [← cancel_mono (kernel.ι w), assoc, he, hb, kernel.lift_ι]
  have : Epi b := by
    rw [show b = kernel.lift w v hvw ≫ e.inv by rw [← hbe, assoc, Iso.hom_inv_id, comp_id]]
    infer_instance
  let S' := ShortComplex.mk (cokernel.desc u d hud) v (by simp [← hb, reassoc_of% h])
  let φ₁ : ShortComplex.mk d v hdv ⟶ S' :=
    { τ₁ := cokernel.π u, τ₂ := 𝟙 L, τ₃ := 𝟙 Y₁ }
  let φ₂ : ShortComplex.mk (cokernel.desc u d hud) b h ⟶ S' :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 L, τ₃ := j, comm₂₃ := by simp [S', hb] }
  have hS' : S'.Exact := (exact_iff_of_epi_of_isIso_of_mono φ₁).1 h₂
  exact { exact := (exact_iff_of_epi_of_isIso_of_mono φ₂).2 hS' }

end CategoryTheory.ShortComplex
