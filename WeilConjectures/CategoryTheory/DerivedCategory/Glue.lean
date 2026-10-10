/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Gluing a complex onto the top degrees of another

Let `α : P ⟶ M` be a morphism of cochain complexes in an abelian category, with `P` strictly
concentrated in degrees `≥ k`, which induces isomorphisms in cohomology in degrees `> k` and an
epimorphism in degree `k`. Then `M` is isomorphic in the derived category to a complex `M'`
containing `P` as a subcomplex which is equal to `M'` in degrees `≥ k`
(`CochainComplex.exists_iso_Q_obj_of_homologyMap`).

This is the replacement of a representative used in the proof of Stacks, Tag 0FPV: the
mapping cone of `α` is acyclic in degrees `≥ k`, hence quasi-isomorphic to its truncation
`C'` in degrees `≤ k - 1`, and `M'` is the mapping cocone of the composite
`C' ⟶ cone(α) ⟶ P[1]`, whose terms are `C'ⁿ ⊕ Pⁿ`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open DerivedCategory HomComplex

/-- If `α : P ⟶ M` induces epimorphisms in cohomology in degrees `≥ k` and monomorphisms in
degrees `> k`, then its mapping cone is acyclic in degrees `≥ k`. -/
lemma isLE_mappingCone_of_homologyMap {P M : CochainComplex C ℤ} (α : P ⟶ M) (k : ℤ)
    (h₁ : ∀ i, k < i → Mono ((homologyFunctor C i).map (Q.map α)))
    (h₂ : ∀ i, k ≤ i → Epi ((homologyFunctor C i).map (Q.map α))) :
    (mappingCone α).IsLE (k - 1) := by
  let T := Q.mapTriangle.obj (mappingCone.triangle α)
  have hT : T ∈ distTriang _ := mappingCone_triangle_distinguished α
  rw [isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ ((homologyFunctorFactors C i).app (mappingCone α)).symm
  have hk : k ≤ i := by lia
  have e₁ : (homologyFunctor C i).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 (h₂ i hk)
  have e₂ : HomologySequence.δ T i (i + 1) = 0 :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1 (h₁ (i + 1) (by lia))
  exact (HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂ e₁ e₂

/-- **Gluing.** Let `α : P ⟶ M` be a morphism of cochain complexes with `P` strictly concentrated
in degrees `≥ k`, inducing isomorphisms in cohomology in degrees `> k` and an epimorphism in
degree `k`. Then there are a complex `M'` isomorphic to `M` in the derived category and a
degreewise monomorphism `j : P ⟶ M'` which is an isomorphism in degrees `≥ k`. -/
theorem exists_iso_Q_obj_of_homologyMap {P M : CochainComplex C ℤ} (α : P ⟶ M) (k : ℤ)
    (h₁ : ∀ i, k < i → IsIso ((homologyFunctor C i).map (Q.map α)))
    (h₂ : Epi ((homologyFunctor C k).map (Q.map α))) :
    ∃ (M' : CochainComplex C ℤ) (j : P ⟶ M'), (∀ i, Mono (j.f i)) ∧
      (∀ i, k ≤ i → IsIso (j.f i)) ∧ Nonempty (Q.obj M' ≅ Q.obj M) := by
  have hC := isLE_mappingCone_of_homologyMap α k (fun i hi ↦ by have := h₁ i hi; infer_instance)
    (fun i hi ↦ by
      obtain rfl | hi := eq_or_lt_of_le hi
      · exact h₂
      · have := h₁ i hi
        infer_instance)
  let C' := (mappingCone α).truncLE (k - 1)
  let ι : C' ⟶ mappingCone α := (mappingCone α).ιTruncLE (k - 1)
  let β : C' ⟶ P⟦(1 : ℤ)⟧ := ι ≫ (mappingCone.triangle α).mor₃
  let j : P ⟶ mappingCocone β := ((mappingCocone.inr β).leftUnshift 0 (by lia)).homOf
  have hj (i : ℤ) : j.f i = (mappingCocone.inr β).1.v (i + -1 + 0) i (by lia) := by
    sorry
  refine ⟨mappingCocone β, j, fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · sorry
  · sorry
  · sorry

end CochainComplex
