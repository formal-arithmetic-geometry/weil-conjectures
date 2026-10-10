/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Degreewise criteria for maps in homology

In an abelian category, a morphism of short complexes which is an epimorphism on the middle
terms and a monomorphism on the right terms induces epimorphisms on cycles and on homology
(`CategoryTheory.ShortComplex.epi_cyclesMap_of_epi_of_mono`,
`CategoryTheory.ShortComplex.epi_homologyMap_of_epi_of_mono`). For homological complexes, this
gives degreewise criteria for `homologyMap φ j` to be an epimorphism or an isomorphism
(`HomologicalComplex.epi_homologyMap_of_epi_of_mono`,
`HomologicalComplex.isIso_homologyMap_of_epi_of_isIso_of_mono`).
-/

@[expose] public section

universe v₁ u₁

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {S₁ S₂ : ShortComplex C}

/-- In an abelian category, a morphism of short complexes which is an epimorphism on the middle
terms and a monomorphism on the right terms induces an epimorphism on cycles. -/
lemma epi_cyclesMap_of_epi_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₂] [Mono φ.τ₃] :
    Epi (cyclesMap φ) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A x
  obtain ⟨A', π, hπ, y, hy⟩ := surjective_up_to_refinements_of_epi φ.τ₂ (x ≫ S₂.iCycles)
  have hy' : y ≫ S₁.g = 0 := by
    rw [← cancel_mono φ.τ₃, Category.assoc, ← φ.comm₂₃, reassoc_of% hy.symm]
    simp
  refine ⟨A', π, hπ, S₁.liftCycles y hy', ?_⟩
  rw [← cancel_mono S₂.iCycles, Category.assoc, Category.assoc, cyclesMap_i,
    liftCycles_i_assoc, hy]

/-- In an abelian category, a morphism of short complexes which is an epimorphism on the middle
terms and a monomorphism on the right terms induces an epimorphism in homology. -/
lemma epi_homologyMap_of_epi_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₂] [Mono φ.τ₃] :
    Epi (homologyMap φ) :=
  have := epi_cyclesMap_of_epi_of_mono φ
  inferInstance

end CategoryTheory.ShortComplex

namespace HomologicalComplex

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- A morphism of complexes which is an epimorphism in degree `i`, an isomorphism in degree `j`
and a monomorphism in degree `k`, where `i ⟶ j ⟶ k`, induces an isomorphism in homology in
degree `j`. -/
lemma isIso_homologyMap_of_epi_of_isIso_of_mono (φ : K ⟶ L) {i j k : ι} (hij : c.prev j = i)
    (hjk : c.next j = k) (h₁ : Epi (φ.f i)) (h₂ : IsIso (φ.f j)) (h₃ : Mono (φ.f k)) :
    IsIso (homologyMap φ j) := by
  subst hij hjk
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' ((shortComplexFunctor C c j).map φ)
    h₁ h₂ h₃

/-- A morphism of complexes which is an epimorphism in degree `j` and a monomorphism in degree `k`,
where `j ⟶ k`, induces an epimorphism in homology in degree `j`. -/
lemma epi_homologyMap_of_epi_of_mono (φ : K ⟶ L) {j k : ι} (hjk : c.next j = k)
    (h₂ : Epi (φ.f j)) (h₃ : Mono (φ.f k)) : Epi (homologyMap φ j) := by
  subst hjk
  have : Epi ((shortComplexFunctor C c j).map φ).τ₂ := h₂
  have : Mono ((shortComplexFunctor C c j).map φ).τ₃ := h₃
  exact ShortComplex.epi_homologyMap_of_epi_of_mono ((shortComplexFunctor C c j).map φ)

end HomologicalComplex
