/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Extensions as cokernels

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in an abelian category, and let
`q : B ⟶ X₃` be an epimorphism which lifts to `φ : B ⟶ X₂`. Then `X₂` is the cokernel of the
morphism `kernel q ⟶ X₁ ⊞ B` given by `(-ψ, kernel.ι q)`, where `ψ : kernel q ⟶ X₁` is the
factorisation of `kernel.ι q ≫ φ` through `X₁`, the cokernel map being `X₁ ⊞ B ⟶ X₂` given by
`(S.f, φ)`. The proofs are by chasing elements up to refinements.

## Main definitions

* `CategoryTheory.ShortComplex.ShortExact.isColimitCokernelCoforkBiprodDesc`: `X₂` is the
  cokernel of `(-ψ, kernel.ι q) : kernel q ⟶ X₁ ⊞ B`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) {B : C} (q : B ⟶ S.X₃) (φ : B ⟶ S.X₂)
  (hφ : φ ≫ S.g = q)

include hφ in
lemma kernel_ι_comp_comp_g : (kernel.ι q ≫ φ) ≫ S.g = 0 := by
  rw [assoc, hφ, kernel.condition]

/-- The factorisation through `S.X₁` of the restriction of a lift `φ : B ⟶ S.X₂` of
`q : B ⟶ S.X₃` to the kernel of `q`. -/
noncomputable def kernelLift : kernel q ⟶ S.X₁ :=
  have := hS.mono_f
  hS.exact.lift (kernel.ι q ≫ φ) (kernel_ι_comp_comp_g q φ hφ)

@[reassoc (attr := simp)]
lemma kernelLift_f : hS.kernelLift q φ hφ ≫ S.f = kernel.ι q ≫ φ :=
  have := hS.mono_f
  hS.exact.lift_f _ _

/-- The morphism `(-ψ, kernel.ι q) : kernel q ⟶ S.X₁ ⊞ B`. -/
noncomputable def kernelToBiprod : kernel q ⟶ S.X₁ ⊞ B :=
  biprod.lift (-hS.kernelLift q φ hφ) (kernel.ι q)

lemma kernelToBiprod_biprodDesc : hS.kernelToBiprod q φ hφ ≫ biprod.desc S.f φ = 0 := by
  simp [kernelToBiprod]

/-- **An extension is a cokernel.** If `q : B ⟶ S.X₃` is an epimorphism lifting to
`φ : B ⟶ S.X₂`, then `(S.f, φ) : S.X₁ ⊞ B ⟶ S.X₂` is a cokernel of
`(-ψ, kernel.ι q) : kernel q ⟶ S.X₁ ⊞ B`. -/
noncomputable def isColimitCokernelCoforkBiprodDesc [Epi q] :
    IsColimit (CokernelCofork.ofπ _ (hS.kernelToBiprod_biprodDesc q φ hφ)) := by
  have := hS.mono_f
  let T := ShortComplex.mk _ _ (hS.kernelToBiprod_biprodDesc q φ hφ)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A y hy
    have h : (y ≫ biprod.fst) ≫ S.f + (y ≫ biprod.snd) ≫ φ = 0 := by
      have hy' : y ≫ biprod.desc S.f φ = 0 := hy
      rwa [biprod.desc_eq, comp_add, ← assoc, ← assoc] at hy'
    refine ⟨A, 𝟙 A, inferInstance, kernel.lift q (y ≫ biprod.snd) ?_, ?_⟩
    · have := congrArg (· ≫ S.g) h
      simpa [hφ] using this
    · apply biprod.hom_ext
      · rw [← cancel_mono S.f]
        simp only [T, kernelToBiprod, id_comp, assoc, biprod.lift_fst, comp_neg, neg_comp,
          kernelLift_f, kernel.lift_ι_assoc]
        rw [← add_eq_zero_iff_eq_neg]
        simpa using h
      · simp [T, kernelToBiprod]
  have : Epi T.g := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A x
    obtain ⟨A', π₁, _, b, hb⟩ := surjective_up_to_refinements_of_epi q (x ≫ S.g)
    obtain ⟨A'', π₂, _, a, ha⟩ := hS.exact.exact_up_to_refinements (π₁ ≫ x - b ≫ φ)
      (by simp [hb, hφ])
    refine ⟨A'', π₂ ≫ π₁, inferInstance, biprod.lift a (π₂ ≫ b), ?_⟩
    have : π₂ ≫ π₁ ≫ x = a ≫ S.f + π₂ ≫ b ≫ φ := by
      rw [← ha, comp_sub, sub_add_cancel]
    simpa [T] using this
  exact hT.gIsCokernel

end ShortComplex.ShortExact

end CategoryTheory
