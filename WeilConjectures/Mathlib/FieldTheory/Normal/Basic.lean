/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Basic

/-!
# Embeddings of a normal extension differ by an automorphism

Two embeddings `φ₁ φ₂ : L →ₐ[K] E` of a normal extension `L/K` into a field `E` have the same
image, hence differ by an automorphism of `L/K`.
-/

@[expose] public section

/-- Two `K`-embeddings of a normal extension `L/K` into a field differ by a `K`-automorphism of
`L`. -/
theorem AlgHom.exists_comp_eq_of_normal {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Normal K L] (φ₁ φ₂ : L →ₐ[K] E) :
    ∃ σ : L ≃ₐ[K] L, φ₁.comp σ.toAlgHom = φ₂ := by
  have hr (φ : L →ₐ[K] E) : φ.range = φ.fieldRange.toSubalgebra :=
    (AlgHom.fieldRange_toSubalgebra φ).symm
  let e (φ : L →ₐ[K] E) : L ≃ₐ[K] φ.fieldRange :=
    (AlgEquiv.ofInjectiveField φ).trans (Subalgebra.equivOfEq _ _ (hr φ))
  have he (φ : L →ₐ[K] E) (x : L) : ((e φ x : φ.fieldRange) : E) = φ x := rfl
  have : Normal K φ₁.fieldRange := Normal.of_algEquiv (e φ₁)
  have h : φ₂.fieldRange = φ₁.fieldRange := by
    have h₀ := AlgHom.fieldRange_of_normal (φ₂.comp (e φ₁).symm.toAlgHom)
    rw [← h₀]
    ext y
    simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e φ₁ x, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  refine ⟨(e φ₂).trans ((IntermediateField.equivOfEq h).trans (e φ₁).symm),
    AlgHom.ext fun x ↦ ?_⟩
  change φ₁ ((e φ₁).symm _) = φ₂ x
  rw [← he φ₁, AlgEquiv.apply_symm_apply]
  rfl
