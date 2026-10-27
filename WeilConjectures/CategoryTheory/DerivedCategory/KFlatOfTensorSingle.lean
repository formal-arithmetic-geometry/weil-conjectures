/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# K-flatness from acyclicity of tensor products with objects

Let `A` be a monoidal abelian category in which `ℤ`-indexed colimits exist, are exact and
commute with the tensor product. We show that a cochain complex `K` is K-flat as soon as the
termwise tensor products `K ⊗ F` and `F ⊗ K` are acyclic for every object `F` of `A`
(`CochainComplex.kFlat_of_forall_acyclic_tensor_single`).

The proof follows [Stacks, Tag 06YN]: the complexes `N` such that `K ⊗ N` and `N ⊗ K` are
acyclic form a triangulated subcategory of the homotopy category containing the single
complexes, hence all bounded complexes; it is closed under `ℤ`-indexed colimits, hence contains
the bounded above complexes (colimits of their stupid truncations) and then all complexes
(colimits of their canonical truncations). In particular it contains the acyclic complexes.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits ZeroObject

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- A complex is acyclic iff any morphism to a zero complex is a quasi-isomorphism. -/
lemma acyclic_iff_quasiIso_of_isZero {K Z : HomologicalComplex C c} (hZ : IsZero Z)
    (f : K ⟶ Z) : K.Acyclic ↔ QuasiIso f := by
  rw [quasiIso_iff]
  exact forall_congr' (fun i ↦ (quasiIsoAt_iff_exactAt' f i (Z.acyclic_of_isZero hZ i)).symm)

/-- Acyclic complexes are stable under colimits of shape `J` when such colimits are exact. -/
lemma acyclic_of_isColimit {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {F : J ⥤ HomologicalComplex C c} {cc : Cocone F}
    (hc : IsColimit cc) (hF : ∀ j, (F.obj j).Acyclic) : cc.pt.Acyclic := by
  let c₂ : Cocone ((Functor.const J).obj (0 : HomologicalComplex C c)) :=
    { pt := 0
      ι := 0 }
  have h₂ : IsColimit c₂ :=
    { desc _ := 0
      fac _ _ := (Limits.isZero_zero _).eq_of_src _ _
      uniq _ _ _ := (Limits.isZero_zero _).eq_of_src _ _ }
  rw [acyclic_iff_quasiIso_of_isZero (Limits.isZero_zero _) (0 : cc.pt ⟶ c₂.pt), ← mem_quasiIso_iff]
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition _ _ cc c₂ hc h₂ 0
    (fun j ↦ by
      rw [mem_quasiIso_iff, ← acyclic_iff_quasiIso_of_isZero (Limits.isZero_zero _)]
      exact hF j) _ (fun _ ↦ (Limits.isZero_zero _).eq_of_tgt _ _)

end HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

/-- The property of a complex `N` that both `K ⊗ N` and `N ⊗ K` are acyclic. -/
def tensorAcyclic (K : CochainComplex A ℤ) : ObjectProperty (CochainComplex A ℤ) :=
  fun N ↦ (K ⊗ N).Acyclic ∧ (N ⊗ K).Acyclic

end CochainComplex

namespace HomotopyCategory

/-- The property of an object `N` of the homotopy category that both `K ⊗ N` and `N ⊗ K`
are acyclic. -/
def tensorAcyclic (K : HomotopyCategory A (.up ℤ)) :
    ObjectProperty (HomotopyCategory A (.up ℤ)) :=
  (subcategoryAcyclic A).inverseImage ((curriedTensor _).obj K) ⊓
    (subcategoryAcyclic A).inverseImage ((curriedTensor _).flip.obj K)

instance (K : HomotopyCategory A (.up ℤ)) : (tensorAcyclic K).IsTriangulated := by
  dsimp only [tensorAcyclic]
  infer_instance

instance (K : HomotopyCategory A (.up ℤ)) : (tensorAcyclic K).IsClosedUnderIsomorphisms := by
  dsimp only [tensorAcyclic]
  infer_instance

lemma tensorAcyclic_quotient_obj_iff (K N : CochainComplex A ℤ) :
    tensorAcyclic ((quotient _ _).obj K) ((quotient _ _).obj N) ↔ K.tensorAcyclic N := by
  simp only [tensorAcyclic, CochainComplex.tensorAcyclic, ObjectProperty.prop_inf_iff,
    ObjectProperty.prop_inverseImage_iff]
  exact and_congr (quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
    (quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

end HomotopyCategory

namespace CochainComplex

variable (K : CochainComplex A ℤ)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Single complexes in degree `0` satisfy `K.tensorAcyclic`. -/
lemma tensorAcyclic_single_obj
    (hR : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hL : ∀ F : A, (((tensorLeft F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) (F : A) :
    K.tensorAcyclic ((HomologicalComplex.single A (.up ℤ) 0).obj F) :=
  ⟨fun n ↦ (hR F n).of_iso
      ((map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) F).app K).symm,
    fun n ↦ (hL F n).of_iso ((map₂HomologicalComplexObjSingleIso (curriedTensor A) F).app K).symm⟩

/-- Strictly bounded complexes satisfy `K.tensorAcyclic`. -/
lemma tensorAcyclic_of_bounded
    (hR : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hL : ∀ F : A, (((tensorLeft F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (N : CochainComplex A ℤ) (a b : ℤ)
    [N.IsStrictlyGE a] [N.IsStrictlyLE b] :
    K.tensorAcyclic N := by
  rw [← HomotopyCategory.tensorAcyclic_quotient_obj_iff]
  refine HomotopyCategory.mem_subcategory_of_strictly_bounded _ N a b (fun n _ _ ↦ ?_)
  exact ObjectProperty.prop_of_iso _
    ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).app (N.X n))
    ((HomotopyCategory.tensorAcyclic_quotient_obj_iff _ _).2
      (K.tensorAcyclic_single_obj hR hL (N.X n)))

/-- `K.tensorAcyclic` is closed under colimits of shape `J` when such colimits are exact and
commute with the tensor product. -/
instance closedUnderColimitsOfShape_tensorAcyclic (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    K.tensorAcyclic.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro N ⟨p⟩
    constructor
    · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)).flip :=
        inferInstanceAs (PreservesColimitsOfShape _ (Functor.map₂CochainComplex _).flip)
      exact HomologicalComplex.acyclic_of_isColimit
        (isColimitOfPreserves ((evaluation _ _).obj K)
          (isColimitOfPreserves (curriedTensor _).flip p.isColimit))
        (fun j ↦ (p.prop_diag_obj j).1)
    · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)) :=
        inferInstanceAs (PreservesColimitsOfShape _ (Functor.map₂CochainComplex _))
      exact HomologicalComplex.acyclic_of_isColimit
        (isColimitOfPreserves ((evaluation _ _).obj K)
          (isColimitOfPreserves (curriedTensor _) p.isColimit))
        (fun j ↦ (p.prop_diag_obj j).2)

variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

/-- Bounded above complexes satisfy `K.tensorAcyclic`, being colimits of their stupid
truncations. -/
lemma tensorAcyclic_of_isStrictlyLE
    (hR : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hL : ∀ F : A, (((tensorLeft F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (N : CochainComplex A ℤ) (b : ℤ) [N.IsStrictlyLE b] :
    K.tensorAcyclic N :=
  ObjectProperty.prop_of_isColimit _
    (N.isColimitCoconeStupidFiltrationGE.whiskerEquivalence Int.opEquivalence.symm)
    (fun i ↦ K.tensorAcyclic_of_bounded hR hL
      (N.stupidTrunc (ComplexShape.embeddingUpIntGE (-i))) (-i) b)

/-- All complexes satisfy `K.tensorAcyclic`, being colimits of their canonical
truncations. -/
lemma tensorAcyclic_of_forall
    (hR : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hL : ∀ F : A, (((tensorLeft F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (N : CochainComplex A ℤ) : K.tensorAcyclic N :=
  ObjectProperty.prop_of_isColimit _ N.isColimitFiltrationLECocone
    (fun n ↦ K.tensorAcyclic_of_isStrictlyLE hR hL (N.truncLE n) n)

end CochainComplex

/-- A cochain complex `K` such that `K ⊗ F` and `F ⊗ K` are acyclic for all objects `F` is
K-flat. -/
theorem CochainComplex.kFlat_of_forall_acyclic_tensor_single
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    (K : CochainComplex A ℤ)
    (hR : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hL : ∀ F : A, (((tensorLeft F).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z _
  obtain ⟨N, rfl⟩ := Z.quotient_obj_surjective
  exact (HomotopyCategory.tensorAcyclic_quotient_obj_iff K N).2
    (K.tensorAcyclic_of_forall hR hL N)
