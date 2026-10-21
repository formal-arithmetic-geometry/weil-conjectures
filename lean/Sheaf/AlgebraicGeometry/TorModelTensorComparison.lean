/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.TorModelRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.AlgebraicGeometry.EtaleConstantModuleTensor
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Computing derived tensor after restriction to constant scalars

Source: Stacks Project, Tags 06YH and 0F1M.
(blueprint: lem-kun-tor-model-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u uC vC wC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

private def tensorComparisonCurried {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (E : C ⥤ D)
    (e : E.prod E ⋙ tensor D ≅ tensor C ⋙ E) :
    (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D) := by
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ (e.app (M, N)).symm) ?_) ?_
  · intro N N' g
    simpa using e.inv.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
  · intro M M' f
    ext N
    simpa using e.inv.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)

private theorem reflects_acyclic
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (K : CochainComplex C ℤ)
    (h : ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz := (h n).isZero_homology.of_iso ((K.sc n).mapHomologyIso F).symm
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

private theorem acyclic_of_iso
    {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (h : K.Acyclic) : L.Acyclic :=
  fun i ↦ (h i).of_iso e

private theorem preserves_acyclic
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (K : CochainComplex C ℤ) (h : K.Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro i
  exact (h i).map F

private theorem kFlat_of_tensor_acyclic
    {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalPreadditive A]
    [∀ j : ℤ, HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {j})) A]
    [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (K : CochainComplex A ℤ)
    (h : ∀ V : CochainComplex A ℤ,
      V.Acyclic → (CochainComplex.mapBifunctor V K (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro V hV
  obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V K (curriedTensor _))).2 (h V hV)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr


private theorem inverse_total_tensor_comparison
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (E : C ⥤ D) (R : D ⥤ C) [E.Additive] [R.Additive]
    [E.IsEquivalence] [R.IsEquivalence]
    (d : E ⋙ R ≅ 𝟭 C) (e : E.prod E ⋙ tensor D ≅ tensor C ⋙ E)
    (K L : CochainComplex D ℤ) :
    Nonempty (((R.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor K L (curriedTensor D))) ≅
      CochainComplex.mapBifunctor ((R.mapHomologicalComplex (.up ℤ)).obj K)
        ((R.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor C)) := by
  let EC := E.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let c : R ⋙ E ≅ 𝟭 _ := Functor.fullyFaithfulCancelRight R (Functor.isoWhiskerLeft R d)
  let dC : EC ⋙ RC ≅ 𝟭 _ := Functor.mapHomologicalComplexCompIso d (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let cC : RC ⋙ EC ≅ 𝟭 _ := Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let τ := (tensorComparisonCurried E (show E.prod E ⋙ tensor _ ≅ tensor _ ⋙ E from e)).hom
  let : IsIso τ := by dsimp only [τ]; infer_instance
  let t := asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ)
    (RC.obj K) (RC.obj L))
  have : ∀ (P Q : CochainComplex
      D ℤ),
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor _) (.up ℤ) :=
    fun _ _ ↦ inferInstance
  let B := (curriedTensor D).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)
  let cKL := (B.mapIso (cC.app K)).app (EC.obj (RC.obj L)) ≪≫
    (B.obj K).mapIso (cC.app L)
  exact ⟨RC.mapIso (t ≪≫ cKL).symm ≪≫
    dC.app (CochainComplex.mapBifunctor (RC.obj K) (RC.obj L) (curriedTensor _))⟩

private theorem kFlat_of_comparison
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalPreadditive D] [HasColimitsOfSize.{0, 0} C]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ M : C, ((curriedTensor C).obj M).PreservesZeroMorphisms]
    [∀ j : ℤ, HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {j})) D]
    [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ D,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (hc : ∀ A B : CochainComplex C ℤ,
      Nonempty (((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor A B (curriedTensor _))) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj B) (curriedTensor _)))
    (K : CochainComplex C ℤ)
    (hK : ∀ A : CochainComplex C ℤ,
      A.Acyclic → (CochainComplex.mapBifunctor A K (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let : FC.IsEquivalence :=
    ((F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor)
  apply kFlat_of_tensor_acyclic
  intro V hV
  let A := FC.objPreimage V
  let e := FC.objObjPreimageIso V
  have hA : A.Acyclic := reflects_acyclic F A (acyclic_of_iso e.symm hV)
  obtain ⟨c⟩ := hc A K
  let B := (curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let d := (B.mapIso e).app (FC.obj K)
  exact acyclic_of_iso (c ≪≫ d) (preserves_acyclic F _ (hK A hA))

private def tensor_single_derived_iso
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{wC} C] [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (M : C) :
    _root_.DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P ((CochainComplex.singleFunctor _ 0).obj M)
        (curriedTensor C)) ≅
      _root_.DerivedCategory.Q.obj P ⊗ (_root_.DerivedCategory.singleFunctor C 0).obj M :=
  _root_.DerivedCategory.Q.mapIso
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P) ≪≫
    (_root_.DerivedCategory.QObjTensorSingleFunctorObjIso P hP M).symm




/-- A tensor equivalence computes tensor with a single complex after localization. -/
private theorem tensor_single_comparison_of_equivalence
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C]
    [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    [HasDerivedCategory.{wC} D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (hc : ∀ A B : CochainComplex C ℤ,
      Nonempty (((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor A B (curriedTensor C))) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj B) (curriedTensor D)))
    (K : CochainComplex C ℤ)
    (hK : ∀ A : CochainComplex C ℤ,
      A.Acyclic → (CochainComplex.mapBifunctor A K (curriedTensor C)).Acyclic)
    (M : C) :
    let FC := F.mapHomologicalComplex (.up ℤ)
    Nonempty (_root_.DerivedCategory.Q.obj
      (FC.obj (CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor C 0).obj M) (curriedTensor C))) ≅
      _root_.DerivedCategory.Q.obj (FC.obj K) ⊗
        (_root_.DerivedCategory.singleFunctor D 0).obj (F.obj M)) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  obtain ⟨c⟩ := hc K ((CochainComplex.singleFunctor C 0).obj M)
  let B := (curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let s := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
  let t := (B.obj (FC.obj K)).mapIso s
  let z := tensor_single_derived_iso (FC.obj K) (kFlat_of_comparison F hc K hK) (F.obj M)
  exact ⟨_root_.DerivedCategory.Q.mapIso (c ≪≫ t) ≪≫ z⟩


/-- The generic comparison using the fixed etale derived tensor. -/
private theorem etale_tensor_single_comparison_of_equivalence
    (A : Type uD) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u})
    [HasColimitsOfSize.{0, 0} (Sheaf T.smallEtaleTopology A)]
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
    [∀ K L : CochainComplex (Sheaf T.smallEtaleTopology A) ℤ,
      CochainComplex.HasMapBifunctor K L (curriedTensor _)]
    (F : C ⥤ Sheaf T.smallEtaleTopology A) [F.Additive] [F.IsEquivalence]
    (hc : ∀ K L : CochainComplex C ℤ,
      Nonempty (((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor K L (curriedTensor C))) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L)
          (curriedTensor (Sheaf T.smallEtaleTopology A))))
    (K : CochainComplex C ℤ)
    (hK : ∀ L : CochainComplex C ℤ,
      L.Acyclic → (CochainComplex.mapBifunctor L K (curriedTensor C)).Acyclic)
    (M : C) :
    let FC := F.mapHomologicalComplex (.up ℤ)
    Nonempty (_root_.DerivedCategory.Q.obj
      (FC.obj (CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor C 0).obj M) (curriedTensor C))) ≅
      ((derivedTensor A T).obj (_root_.DerivedCategory.Q.obj (FC.obj K))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (F.obj M))) := by
  exact tensor_single_comparison_of_equivalence F hc K hK M


attribute [local irreducible] torModelRestriction

section TensorComparison
variable (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})

local instance : (T.smallEtaleTopology.W.inverseImage
    (PresheafOfModules.toPresheaf.{u + 1} (torModelRing Λ T).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_independentCoefficients (torModelCoefficientRing Λ T)
local instance : MonoidalCategory (SheafOfModules.{u + 1} (torModelRing Λ T)) :=
  SheafOfModules.monoidalCategory (torModelCoefficientRing Λ T)
local instance : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u + 1} (torModelRing Λ T)) := by
  change HasColimitsOfSize.{0, 0} (SheafOfModules.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)))
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1, u + 1, u + 2} _
local instance : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 1} Λ) :=
  hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1, u + 1, u + 2} _

local instance : HasColimitsOfSize.{0, 0}
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Sheaf.instHasColimitsOfSize (J := T.smallEtaleTopology) (D := ModuleCat.{u + 1} Λ)

local instance : (curriedTensor
    (SheafOfModules.{u + 1} (torModelRing Λ T))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (torModelCoefficientRing Λ T)
local instance (M : SheafOfModules.{u + 1} (torModelRing Λ T)) :
    ((curriedTensor _).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (torModelCoefficientRing Λ T) M

local instance (K L : CochainComplex
    (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) :
    CochainComplex.HasMapBifunctor K L (curriedTensor _) := by
  intro n
  exact HasColimitsOfShape.has_colimit _

local instance (K L : CochainComplex
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    CochainComplex.HasMapBifunctor K L (curriedTensor _) := by
  intro n
  exact HasColimitsOfShape.has_colimit _

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_total_tensor_comparison
    (K L : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ) :
    let R : SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) := torModelRestriction Λ T
    let RC := R.mapHomologicalComplex (.up ℤ)
    Nonempty (RC.obj (CochainComplex.mapBifunctor K L (curriedTensor _)) ≅
      CochainComplex.mapBifunctor (RC.obj K) (RC.obj L)
        (curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) := by
  let E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      SheafOfModules.{u + 1} (torModelRing Λ T) :=
    Scheme.etaleSumTensorTestRealization T Λ
  let R := torModelRestriction Λ T
  let : E.IsEquivalence := Scheme.etaleSumTensorTestRealization_isEquivalence T Λ
  let : R.IsEquivalence := torModelRestriction_isEquivalence T Λ
  let : E.Additive := Functor.additive_of_preserves_binary_products E
  let : R.Additive := torModelRestriction_additive Λ T
  let := SheafOfModules.tensorPreadditive (torModelCoefficientRing Λ T)
  exact inverse_total_tensor_comparison E R (torModelRealizationRestrictionIso Λ T)
    (Classical.choice (Scheme.etaleConstantModule_tensor_comparison T Λ)) K L



/-- Restricting the total tensor of a K-flat complex and a sheaf in degree zero
computes the existing derived tensor on module-valued sheaves.
Source: Stacks Project, Tags 06YH, 0H7J and 0F1M
(blueprint: lem-kun-tor-model-tensor-comparison).

Proof: constant-scalar restriction is the equivalence which extends the action
uniquely along the locally bijective constant-ring sheafification unit. It is exact.
The balanced tensor universal property identifies the restriction of the sheafified
ring-sheaf tensor with the sheafified constant-scalar tensor. These identifications
commute with differentials and direct sums, so they identify total tensor complexes.
Exactness and the inverse equivalence carry acyclic complexes to acyclic complexes;
thus the restriction of K is categorically K-flat. The K-flat localization counit
computes derived tensor by the ordinary total tensor with any second complex.
Apply it to the sheaf in degree zero, and use the single-complex/localization
comparison. The result uses the fixed derived tensor of etale module sheaves. -/
theorem torModel_tensor_single_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u + 1} (torModelRing Λ T)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := torModelCoefficientRing Λ T) K)
    (M : SheafOfModules.{u + 1} (torModelRing Λ T)) :
    let R : SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) := torModelRestriction Λ T
    let RC := R.mapHomologicalComplex (.up ℤ)
    Nonempty (_root_.DerivedCategory.Q.obj
      (RC.obj (CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor _ 0).obj M) (curriedTensor _))) ≅
      (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
        (_root_.DerivedCategory.Q.obj (RC.obj K))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (R.obj M)))) := by
  let := torModelRestriction_isEquivalence T Λ
  let := SheafOfModules.tensorPreadditive (torModelCoefficientRing Λ T)
  exact etale_tensor_single_comparison_of_equivalence (ModuleCat.{u + 1} Λ) T
    (torModelRestriction Λ T)
    (restriction_total_tensor_comparison Λ T) K hK M

end TensorComparison
end AlgebraicGeometry.Etale
