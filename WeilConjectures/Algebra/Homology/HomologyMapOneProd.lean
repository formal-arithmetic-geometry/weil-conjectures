/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomologyPiAb

/-!
# A bijectivity criterion for a pair of maps on `H¹`

For morphisms `f₁ : C ⟶ D₁` and `f₂ : C ⟶ D₂` of cochain complexes of abelian groups, we give
an elementwise criterion for `H¹(C) → H¹(D₁) × H¹(D₂)` to be bijective.

## Main statements

- `HomologicalComplex.bijective_homologyMap_one_prod`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace HomologicalComplex

/-- Let `f₁ : C ⟶ D₁` and `f₂ : C ⟶ D₂` be morphisms of cochain complexes of abelian groups.
Suppose that a `1`-cocycle of `C` whose images are coboundaries is a coboundary, and that every
pair of `1`-cocycles of `D₁` and `D₂` is the image of a `1`-cocycle of `C`. Then
`H¹(C) → H¹(D₁) × H¹(D₂)` is bijective. -/
lemma bijective_homologyMap_one_prod {C D₁ D₂ : CochainComplex AddCommGrpCat.{u} ℕ}
    (f₁ : C ⟶ D₁) (f₂ : C ⟶ D₂)
    (hinj : ∀ c : C.X 1, C.d 1 2 c = 0 → (∃ b, D₁.d 0 1 b = f₁.f 1 c) →
      (∃ b, D₂.d 0 1 b = f₂.f 1 c) → ∃ b, C.d 0 1 b = c)
    (hsurj : ∀ e₁ : D₁.X 1, D₁.d 1 2 e₁ = 0 → ∀ e₂ : D₂.X 1, D₂.d 1 2 e₂ = 0 →
      ∃ c : C.X 1, C.d 1 2 c = 0 ∧ f₁.f 1 c = e₁ ∧ f₂.f 1 c = e₂) :
    Function.Bijective fun x : C.homology 1 ↦ (homologyMap f₁ 1 x, homologyMap f₂ 1 x) := by
  have hprev : (ComplexShape.up ℕ).prev 1 = 0 := by simp
  have hnext : (ComplexShape.up ℕ).next 1 = 2 := by simp
  -- a cycle maps to a boundary iff its image in homology vanishes
  have hbd {D : CochainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (z : C.cycles 1)
      (hz : homologyMap f 1 (C.homologyπ 1 z) = 0) : ∃ b, D.d 0 1 b = f.f 1 (C.iCycles 1 z) := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply,
      D.ab_homologyπ_eq_zero_iff' 0 1 hprev] at hz
    obtain ⟨b, hb⟩ := hz
    refine ⟨b, ?_⟩
    rw [← D.toCycles_i 0 1, ConcreteCategory.comp_apply, hb, ← ConcreteCategory.comp_apply,
      cyclesMap_i, ConcreteCategory.comp_apply]
  have hcyc {D : CochainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (z : C.cycles 1)
      (z' : D.cycles 1) (h : f.f 1 (C.iCycles 1 z) = D.iCycles 1 z') :
      homologyMap f 1 (C.homologyπ 1 z) = D.homologyπ 1 z' := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply]
    congr 1
    refine D.ab_iCycles_injective 1 ?_
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, h]
  let F : C.homology 1 →+ D₁.homology 1 × D₂.homology 1 :=
    (homologyMap f₁ 1).hom.prod (homologyMap f₂ 1).hom
  refine ⟨(injective_iff_map_eq_zero F).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := C.ab_homologyπ_surjective 1 x
    obtain ⟨b, hb⟩ := hinj (C.iCycles 1 z)
      (by rw [← ConcreteCategory.comp_apply, iCycles_d, AddCommGrpCat.zero_apply])
      (hbd f₁ z (congrArg Prod.fst hx)) (hbd f₂ z (congrArg Prod.snd hx))
    rw [C.ab_homologyπ_eq_zero_iff' 0 1 hprev]
    refine ⟨b, C.ab_iCycles_injective 1 ?_⟩
    rw [← ConcreteCategory.comp_apply, toCycles_i, hb]
  · obtain ⟨z₁, hz₁⟩ := D₁.ab_homologyπ_surjective 1 y.1
    obtain ⟨z₂, hz₂⟩ := D₂.ab_homologyπ_surjective 1 y.2
    obtain ⟨c, hc, hc₁, hc₂⟩ := hsurj (D₁.iCycles 1 z₁)
      (by rw [← ConcreteCategory.comp_apply, iCycles_d, AddCommGrpCat.zero_apply])
      (D₂.iCycles 1 z₂)
      (by rw [← ConcreteCategory.comp_apply, iCycles_d, AddCommGrpCat.zero_apply])
    obtain ⟨z, hz⟩ := C.ab_exists_iCycles_eq' 1 2 hnext c hc
    refine ⟨C.homologyπ 1 z, Prod.ext ?_ ?_⟩
    · exact (hcyc f₁ z z₁ (by rw [hz, hc₁])).trans hz₁
    · exact (hcyc f₂ z z₂ (by rw [hz, hc₂])).trans hz₂

end HomologicalComplex
