/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The short exact sequences cut out of the homology sequence

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian
category, with a shift sequence `n ↦ Fⁿ`, and let `T = (X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧)` be a
distinguished triangle. The long exact homology sequence

`Fⁿ(X₁) ⟶ Fⁿ(X₂) ⟶ Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂)`

breaks into the short exact sequence

`0 ⟶ coker(Fⁿ(X₁) ⟶ Fⁿ(X₂)) ⟶ Fⁿ(X₃) ⟶ ker(Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂)) ⟶ 0`.

## Main definitions

- `CategoryTheory.Functor.homologySequenceCokernelKernel`: this short complex.

## Main statements

- `CategoryTheory.Functor.homologySequenceCokernelKernel_shortExact`: it is short exact.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits Pretriangulated

variable {C A : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Category A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- The short complex `coker(Fⁿ⁰(T.mor₁)) ⟶ Fⁿ⁰(T.obj₃) ⟶ ker(Fⁿ¹(T.mor₁))` cut out of the
homology sequence of a distinguished triangle `T` by a homological functor `F`, for
`n₀ + 1 = n₁`. -/
noncomputable def homologySequenceCokernelKernel (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex A :=
  ShortComplex.mk (cokernel.desc _ _ (F.homologySequence_comp T hT n₀))
    (kernel.lift _ _ (F.homologySequenceδ_comp T hT n₀ n₁ h)) (by
      rw [← cancel_epi (cokernel.π _), ← cancel_mono (kernel.ι _)]
      simp [F.comp_homologySequenceδ T hT n₀ n₁ h])

/-- The short complex `coker(Fⁿ⁰(T.mor₁)) ⟶ Fⁿ⁰(T.obj₃) ⟶ ker(Fⁿ¹(T.mor₁))` of a
distinguished triangle `T` is short exact: this is the long exact homology sequence of `T`. -/
lemma homologySequenceCokernelKernel_shortExact (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.homologySequenceCokernelKernel T hT n₀ n₁ h).ShortExact where
  exact := by
    let S' : ShortComplex A := ShortComplex.mk
      (cokernel.desc _ _ (F.homologySequence_comp T hT n₀)) (F.homologySequenceδ T n₀ n₁ h) (by
        rw [← cancel_epi (cokernel.π _)]
        simp [F.comp_homologySequenceδ T hT n₀ n₁ h])
    let φ : ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT n₀ n₁ h) ⟶ S' :=
      { τ₁ := cokernel.π _
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let ψ : F.homologySequenceCokernelKernel T hT n₀ n₁ h ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι _
        comm₂₃ := by simp [homologySequenceCokernelKernel, S'] }
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ,
      ← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact F.homologySequence_exact₃ T hT n₀ n₁ h
  mono_f := (F.homologySequence_exact₂ T hT n₀).mono_cokernelDesc
  epi_g := (F.homologySequence_exact₁ T hT n₀ n₁ h).epi_kernelLift

end CategoryTheory.Functor
