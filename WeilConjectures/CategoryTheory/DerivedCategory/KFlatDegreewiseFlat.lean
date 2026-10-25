/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!

# K-flat resolutions by complexes of flat objects

Let `A` be a monoidal abelian category with functorial flat resolutions in which `ℤ`-indexed
colimits exist, are exact and commute with the tensor product. Every cochain complex `K` admits
a quasi-isomorphism `P ⟶ K` from a K-flat complex `P` all of whose terms are flat
(`CochainComplex.exists_quasiIso_kFlat_of_flat`): the functorial flat resolution of `K` is a
sequential colimit of bounded above complexes of flat objects, and flat objects are closed under
sequential colimits.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [HasCountableCoproducts A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

/-- The functorial flat resolution of a complex consists of flat objects: it is a sequential
colimit of complexes of flat objects. -/
lemma flat_resolutionFunctor_obj_X {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasFiniteCoproducts C] {ι : C ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
    (Λ : Abelian.LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
    (hι : ι.essImage ≤ ObjectProperty.flat) (K : CochainComplex A ℤ) (n : ℤ) :
    ObjectProperty.flat ((Λ.resolutionFunctor.obj K).X n) := by
  have := closedUnderColimitsOfShape_flat A ℤ
  let e := Λ.colimitOfShapeFlatResolutionFunctorObj hι K
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n) e.isColimit)
    (fun j ↦ (e.prop_diag_obj j).1 n)

/-- Every cochain complex `K` admits a quasi-isomorphism `P ⟶ K` from a K-flat complex `P` all
of whose terms are flat. -/
lemma exists_quasiIso_kFlat_of_flat [Abelian.HasFunctorialFlatResolution A]
    (K : CochainComplex A ℤ) :
    ∃ (P : CochainComplex A ℤ) (π : P ⟶ K), QuasiIso π ∧
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P ∧ ∀ n, ObjectProperty.flat (P.X n) := by
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
  exact ⟨_, Λ.reduced.resolutionNatTrans.app K, inferInstance,
    Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K,
    flat_resolutionFunctor_obj_X Λ.reduced ObjectProperty.flat.essImage_ι_le K⟩

end CochainComplex
