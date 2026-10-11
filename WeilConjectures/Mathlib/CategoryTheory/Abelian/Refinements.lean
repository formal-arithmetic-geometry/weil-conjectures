/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# A presentation of the middle term of a short exact sequence

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in an abelian category and let
`s : P ⟶ X₂` be a morphism such that `s ≫ g : P ⟶ X₃` is an epimorphism. Then `X₂` is the
cokernel of the morphism `kernel (s ≫ g) ⟶ P ⊞ X₁` given by the inclusion and minus the map
induced by `s`: the sequence `kernel (s ≫ g) ⟶ P ⊞ X₁ ⟶ X₂ ⟶ 0` is exact. This is proved with
the refinements of `Mathlib/CategoryTheory/Abelian/Refinements.lean`.

## Main definitions

* `CategoryTheory.ShortComplex.ShortExact.presentation`: the complex
  `kernel (s ≫ g) ⟶ P ⊞ X₁ ⟶ X₂`.
* `CategoryTheory.ShortComplex.ShortExact.isoCokernelPresentation`: `X₂` is the cokernel of its
  first map.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C} (hS : S.ShortExact)
  {P : C} (s : P ⟶ S.X₂)

/-- For a short exact sequence `S` and a morphism `s : P ⟶ S.X₂`, the map from the kernel of
`s ≫ S.g` to `S.X₁` induced by `s`. -/
noncomputable def kernelToX₁ : kernel (s ≫ S.g) ⟶ S.X₁ :=
  have := hS.mono_f
  hS.exact.lift (kernel.ι (s ≫ S.g) ≫ s) (by rw [Category.assoc, kernel.condition])

@[reassoc (attr := simp)]
lemma kernelToX₁_f : hS.kernelToX₁ s ≫ S.f = kernel.ι (s ≫ S.g) ≫ s := by
  have := hS.mono_f
  exact hS.exact.lift_f _ _

/-- The complex `kernel (s ≫ S.g) ⟶ P ⊞ S.X₁ ⟶ S.X₂` attached to a short exact sequence `S` and
a morphism `s : P ⟶ S.X₂`. It is exact (`presentation_exact`), and its second map is an
epimorphism when `s ≫ S.g` is (`epi_presentation_g`): the middle term of `S` is presented by `P`,
`S.X₁` and the kernel of `s ≫ S.g`. -/
@[simps]
noncomputable def presentation : ShortComplex C where
  X₁ := kernel (s ≫ S.g)
  X₂ := P ⊞ S.X₁
  X₃ := S.X₂
  f := biprod.lift (kernel.ι (s ≫ S.g)) (-hS.kernelToX₁ s)
  g := biprod.desc s S.f
  zero := by simp

lemma presentation_exact : (hS.presentation s).Exact := by
  have := hS.mono_f
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  change A ⟶ P ⊞ S.X₁ at x
  change x ≫ biprod.desc s S.f = 0 at hx
  have h₁ : x ≫ biprod.fst ≫ s = -(x ≫ biprod.snd ≫ S.f) := by
    rw [eq_neg_iff_add_eq_zero, ← hx]
    simp [← Preadditive.comp_add, biprod.desc_eq]
  have h₂ : (x ≫ biprod.fst) ≫ s ≫ S.g = 0 := by
    rw [Category.assoc, ← Category.assoc biprod.fst, ← Category.assoc x, h₁]
    simp
  refine ⟨A, 𝟙 A, inferInstance, kernel.lift _ _ h₂, ?_⟩
  change 𝟙 A ≫ x = kernel.lift _ _ h₂ ≫ biprod.lift (kernel.ι (s ≫ S.g)) (-hS.kernelToX₁ s)
  refine biprod.hom_ext _ _ (by simp) ((cancel_mono S.f).1 ?_)
  simp [h₁]

lemma epi_presentation_g [Epi (s ≫ S.g)] : Epi (hS.presentation s).g := by
  have := hS.mono_f
  rw [epi_iff_surjective_up_to_refinements]
  intro A y
  change A ⟶ S.X₂ at y
  obtain ⟨A', π, hπ, z, hz⟩ := surjective_up_to_refinements_of_epi (s ≫ S.g) (y ≫ S.g)
  have h : (π ≫ y - z ≫ s) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hz, Category.assoc, sub_self]
  refine ⟨A', π, hπ, biprod.lift z (hS.exact.lift _ h), ?_⟩
  change π ≫ y = biprod.lift z (hS.exact.lift _ h) ≫ biprod.desc s S.f
  rw [biprod.lift_desc, ShortComplex.Exact.lift_f, add_sub_cancel]

/-- The middle term of a short exact sequence `S` is the cokernel of the first map of
`presentation`, if `s ≫ S.g` is an epimorphism. -/
noncomputable def isoCokernelPresentation [Epi (s ≫ S.g)] :
    S.X₂ ≅ cokernel (hS.presentation s).f :=
  have := hS.epi_presentation_g s
  ((hS.presentation_exact s).gIsCokernel).coconePointUniqueUpToIso (colimit.isColimit _)

end CategoryTheory.ShortComplex.ShortExact
