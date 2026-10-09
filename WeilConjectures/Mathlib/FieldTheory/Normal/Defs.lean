/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Defs

/-!
# Embeddings of a normal extension differ by an automorphism

Two `F`-embeddings of a normal extension `N/F` into a field `E` differ by an automorphism of
`N`.
-/

@[expose] public section

/-- Two `F`-algebra maps `N →ₐ[F] E` out of a normal extension `N/F` differ by an automorphism
of `N`. -/
lemma Normal.exists_algEquiv_comp_eq {F N E : Type*} [Field F] [Field N] [Field E]
    [Algebra F N] [Algebra F E] [Normal F N] (β₁ β₂ : N →ₐ[F] E) :
    ∃ σ : N ≃ₐ[F] N, β₂ = β₁.comp σ.toAlgHom := by
  let := β₁.toRingHom.toAlgebra
  have : IsScalarTower F N E := .of_algebraMap_eq fun x ↦ (β₁.commutes x).symm
  refine ⟨Normal.algHomEquivAut F E N β₂, ?_⟩
  conv_lhs => rw [← (Normal.algHomEquivAut F E N).symm_apply_apply β₂]
  rfl
