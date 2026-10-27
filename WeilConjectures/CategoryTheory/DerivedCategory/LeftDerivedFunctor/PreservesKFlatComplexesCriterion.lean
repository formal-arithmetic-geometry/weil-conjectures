/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# A criterion for a functor to preserve K-flat complexes

Let `F : C ⥤ D` be an additive functor between monoidal abelian categories. We reduce the
statement that `F` sends K-flat complexes to K-flat complexes
(`CategoryTheory.Functor.PreservesKFlatComplexes`) to two inputs, following the reduction in
[Stacks, Tag 0DEN]:

* every K-flat complex `P` receives a quasi-isomorphism `Q ⟶ P` from a K-flat complex `Q` with
  `F Q` K-flat;
* `F` sends *acyclic* K-flat complexes to K-flat complexes.

Indeed, the mapping cone of `Q ⟶ P` is then acyclic and K-flat, the K-flat complexes forming a
triangulated subcategory of the homotopy category, and `F` applied to the triangle
`Q ⟶ P ⟶ cone ⟶ Q[1]` is a distinguished triangle with two K-flat vertices.

When `C` has functorial flat resolutions and `F` preserves flat objects and `ℤ`-indexed
colimits, the first input is supplied by the functorial flat resolutions, which are `ℤ`-indexed
colimits of bounded above complexes of flat objects
(`CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj`).

## Main results

- `CategoryTheory.Functor.preservesKFlatComplexes_of_exists_quasiIso`: the general criterion.
- `CategoryTheory.Functor.preservesKFlatComplexes_of_preservesFlat`: the criterion when `F`
  preserves flat objects and `ℤ`-indexed colimits.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

section General

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The mapping cone of a morphism between K-flat complexes is K-flat. -/
lemma kFlat_mappingCone {Q P : CochainComplex C ℤ} (π : Q ⟶ P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat (CochainComplex.mappingCone π) := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hQ hP ⊢
  have h := (HomotopyCategory.quasiIso C (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₃
    (CochainComplex.mappingCone.triangleh π)
    (HomotopyCategory.mappingCone_triangleh_distinguished π) hQ hP
  exact h

/-- **Criterion for preserving K-flat complexes.** An additive functor `F` preserves K-flat
complexes if every K-flat complex `P` receives a quasi-isomorphism from a K-flat complex `Q`
with `F Q` K-flat, and if `F` sends acyclic K-flat complexes to K-flat complexes. -/
theorem preservesKFlatComplexes_of_exists_quasiIso (F : C ⥤ D) [F.Additive]
    (hres : ∀ (P : CochainComplex C ℤ), (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
      ∃ (Q : CochainComplex C ℤ) (π : Q ⟶ P), QuasiIso π ∧
        (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q ∧
        (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
          ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (hacyclic : ∀ (K : CochainComplex C ℤ), K.Acyclic →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K →
        (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) :
    F.PreservesKFlatComplexes where
  kFlat_map P hP := by
    obtain ⟨Q, π, hπ, hQ, hFQ⟩ := hres P hP
    let := HasDerivedCategory.standard C
    have hcone : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone π)) :=
      hacyclic _ ((DerivedCategory.quasiIso_iff_acyclic_mappingCone π).1 hπ)
        (kFlat_mappingCone π hQ hP)
    rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hFQ hcone ⊢
    have hT := (F.mapHomotopyCategory (.up ℤ)).map_distinguished
      (CochainComplex.mappingCone.triangleh π)
      (HomotopyCategory.mappingCone_triangleh_distinguished π)
    have h₁ : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingCone.triangleh π)).obj₁ :=
      (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.prop_of_iso
        ((F.mapHomotopyCategoryFactors (.up ℤ)).app Q).symm hFQ
    have h₃ : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingCone.triangleh π)).obj₃ :=
      (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.prop_of_iso
        ((F.mapHomotopyCategoryFactors (.up ℤ)).app _).symm hcone
    have h₂ := (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₂ _ hT h₁ h₃
    exact (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.prop_of_iso
      ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) h₂

end General
section PreservesFlat

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]

/-- **Criterion for preserving K-flat complexes, flat case.** If `C` has functorial flat
resolutions, an additive functor `F` preserving flat objects and `ℤ`-indexed colimits preserves
K-flat complexes as soon as it sends acyclic K-flat complexes to K-flat complexes: the
functorial flat resolutions provide the quasi-isomorphisms `Q ⟶ P` of
`Functor.preservesKFlatComplexes_of_exists_quasiIso`. -/
theorem preservesKFlatComplexes_of_preservesFlat (F : C ⥤ D) [F.Additive] [F.PreservesFlat]
    [PreservesColimitsOfShape ℤ F]
    (hacyclic : ∀ (K : CochainComplex C ℤ), K.Acyclic →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K →
        (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) :
    F.PreservesKFlatComplexes := by
  refine F.preservesKFlatComplexes_of_exists_quasiIso (fun P _ ↦ ?_) hacyclic
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by
        intros
        simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  exact ⟨Λ.resolutionFunctor.obj P, Λ.resolutionNatTrans.app P, inferInstance,
    Λ.kFlat_resolutionFunctor_obj hι P,
    F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ hι P⟩

end PreservesFlat

end CategoryTheory.Functor
