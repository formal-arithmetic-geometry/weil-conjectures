/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitCounit
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Unit laws on K-flat representatives

## References

* Stacks Project, Tag 079U
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

private theorem tensorUnit_left_square
    {K₁ K₂ D₁ D₂ : Type*}
    [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
    [MonoidalCategory K₁] [MonoidalCategory K₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : K₁ ⥤ D₁) (Q₂ : K₂ ⥤ D₂) [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    (F : K₁ ⥤ K₂) (G : D₁ ⥤ D₂)
    (δ : curriedTensorPost G ⟶ curriedTensorPre G)
    (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
    (a : K₁) (u : 𝟙_ K₂ ≅ F.obj (𝟙_ K₁))
    (φ : F.obj (𝟙_ K₁ ⊗ a) ≅ F.obj (𝟙_ K₁) ⊗ F.obj a)
    (η : 𝟙_ D₂ ≅ G.obj (𝟙_ D₁))
    [IsIso (Functor.LaxMonoidal.ε Q₂)] [IsIso (e a)]
    (hη : η.inv = G.map (Functor.LaxMonoidal.ε Q₁) ≫ e (𝟙_ K₁) ≫
      Q₂.map u.inv ≫ inv (Functor.LaxMonoidal.ε Q₂))
    (he : G.map (Q₁.map (λ_ a).inv) ≫ e (𝟙_ K₁ ⊗ a) =
      e a ≫ Q₂.map (F.map (λ_ a).inv))
    (hδ : (δ.app (Q₁.obj (𝟙_ K₁))).app (Q₁.obj a) ≫
      (e (𝟙_ K₁) ⊗ₘ e a) ≫ Functor.LaxMonoidal.μ Q₂ (F.obj (𝟙_ K₁)) (F.obj a) =
      G.map (Functor.LaxMonoidal.μ Q₁ (𝟙_ K₁) a) ≫
        e (𝟙_ K₁ ⊗ a) ≫ Q₂.map φ.hom)
    (hu : F.map (λ_ a).inv ≫ φ.hom ≫ u.inv ▷ F.obj a = (λ_ (F.obj a)).inv) :
    (λ_ (G.obj (Q₁.obj a))).inv = G.map (λ_ (Q₁.obj a)).inv ≫
      (δ.app (𝟙_ D₁)).app (Q₁.obj a) ≫ η.inv ▷ G.obj (Q₁.obj a) := by
  have := Functor.LaxMonoidal.isIso_μ_tensorUnit_left Q₂ (F.obj a)
  open Category Functor.LaxMonoidal Functor.OplaxMonoidal in
  rw [hη, ← cancel_mono ((ε Q₂ ⊗ₘ e a) ≫ μ Q₂ (𝟙_ K₂) (F.obj a))]
  rw [leftUnitor_inv_comp_tensorHom_assoc, left_unitality_inv]
  simp only [assoc]
  rw [whiskerRight_comp_tensorHom_assoc]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [comp_tensorHom_comp_comp]
  simp only [assoc]
  rw [μ_natural_left, app_app_comp_whiskerRight_assoc, reassoc_of% hδ,
    ← G.map_comp_assoc, ← G.map_comp_assoc, assoc (λ_ (Q₁.obj a)).inv,
    left_unitality_inv, reassoc_of% he,
    ← Q₂.map_comp, ← Q₂.map_comp, hu]

private theorem tensorUnit_right_square
    {K₁ K₂ D₁ D₂ : Type*}
    [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
    [MonoidalCategory K₁] [MonoidalCategory K₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : K₁ ⥤ D₁) (Q₂ : K₂ ⥤ D₂) [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    (F : K₁ ⥤ K₂) (G : D₁ ⥤ D₂)
    (δ : curriedTensorPost G ⟶ curriedTensorPre G)
    (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
    (a : K₁) (u : 𝟙_ K₂ ≅ F.obj (𝟙_ K₁))
    (φ : F.obj (a ⊗ 𝟙_ K₁) ≅ F.obj a ⊗ F.obj (𝟙_ K₁))
    (η : 𝟙_ D₂ ≅ G.obj (𝟙_ D₁))
    [IsIso (Functor.LaxMonoidal.ε Q₂)] [IsIso (e a)]
    (hη : η.inv = G.map (Functor.LaxMonoidal.ε Q₁) ≫ e (𝟙_ K₁) ≫
      Q₂.map u.inv ≫ inv (Functor.LaxMonoidal.ε Q₂))
    (he : G.map (Q₁.map (ρ_ a).inv) ≫ e (a ⊗ 𝟙_ K₁) =
      e a ≫ Q₂.map (F.map (ρ_ a).inv))
    (hδ : (δ.app (Q₁.obj a)).app (Q₁.obj (𝟙_ K₁)) ≫
      (e a ⊗ₘ e (𝟙_ K₁)) ≫ Functor.LaxMonoidal.μ Q₂ (F.obj a) (F.obj (𝟙_ K₁)) =
      G.map (Functor.LaxMonoidal.μ Q₁ a (𝟙_ K₁)) ≫
        e (a ⊗ 𝟙_ K₁) ≫ Q₂.map φ.hom)
    (hu : F.map (ρ_ a).inv ≫ φ.hom ≫ F.obj a ◁ u.inv = (ρ_ (F.obj a)).inv) :
    (ρ_ (G.obj (Q₁.obj a))).inv = G.map (ρ_ (Q₁.obj a)).inv ≫
      (δ.app (Q₁.obj a)).app (𝟙_ D₁) ≫ G.obj (Q₁.obj a) ◁ η.inv := by
  have := Functor.LaxMonoidal.isIso_μ_tensorUnit_right Q₂ (F.obj a)
  open Category Functor.LaxMonoidal Functor.OplaxMonoidal in
  rw [hη, ← cancel_mono ((e a ⊗ₘ ε Q₂) ≫ μ Q₂ (F.obj a) (𝟙_ K₂))]
  rw [rightUnitor_inv_comp_tensorHom_assoc, right_unitality_inv]
  simp only [assoc]
  rw [whiskerLeft_comp_tensorHom_assoc]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [tensorHom_comp_comp_comp]
  simp only [assoc]
  rw [μ_natural_right, app_app_comp_whiskerLeft_assoc, reassoc_of% hδ,
    ← G.map_comp_assoc, ← G.map_comp_assoc, assoc (ρ_ (Q₁.obj a)).inv,
    right_unitality_inv, reassoc_of% he,
    ← Q₂.map_comp, ← Q₂.map_comp, hu]

private theorem tensorUnit_counit_kFlat_isIso {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  have hFE : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      F₀, hF₀, hmap₀, hF₀add, ε₀, hderived₀, htri, hε₀⟩ :=
    (derivedPullback_spec g)
  have hF₀E : F₀ = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF₀ (fun _ _ a ↦ hmap₀ a)
  subst F₀
  have := hε₀ P hP
  let W := HomotopyCategory.quasiIso
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W := hε
  have : (derivedPullback g).IsLeftDerivedFunctor ε₀ W := hderived₀
  let e := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε ε₀ W
  have he : e.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj P)) ≫
      ε₀.app ((HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj P) := by
    simp [e, Functor.leftDerivedNatIso]
  rw [← he]
  infer_instance

private theorem tensorUnit_complex_left
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, Limits.PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, Limits.PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive] (mF : F.CoreMonoidal) (P : CochainComplex C ℤ)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex C ℤ) ⊗ P) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ⊗
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (hφ : ∀ n : ℤ, F.map (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex C ℤ)) P 0 n n
      (zero_add n)) ≫ φ.hom.f n =
      (mF.μIso ((𝟙_ (CochainComplex C ℤ)).X 0) (P.X n)).inv ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)))
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) 0 n n (zero_add n)) :
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    let u := (HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
    FC.map (λ_ P).inv ≫ φ.hom ≫ u.inv ▷ FC.obj P = (λ_ (FC.obj P)).inv := by
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let U : CochainComplex C ℤ := 𝟙_ _
  let u : 𝟙_ (CochainComplex D ℤ) ≅ FC.obj U :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
  have hu0 : u.inv.f 0 =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C)).hom ≫
        mF.εIso.inv ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ D)).inv := by
    simp [u, HomologicalComplex.single_map_f_self]
  let := mF.toMonoidal
  ext i : 1
  have h₁ : (λ_ P).inv.f i = (HomologicalComplex.leftUnitor' P).inv i := rfl
  have h₂ : (λ_ (FC.obj P)).inv.f i =
      (HomologicalComplex.leftUnitor' (FC.obj P)).inv i := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, h₁, h₂,
    HomologicalComplex.leftUnitor'_inv, HomologicalComplex.leftUnitor'_inv]
  change _ ≫ _ ≫
    (HomologicalComplex.mapBifunctorMap u.inv (𝟙 (FC.obj P)) (curriedTensor _)
      (ComplexShape.up ℤ)).f i = _
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (hφ i)]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app,
    curriedTensor_obj_map, hu0]
  change _ ≫ _ ≫ Functor.OplaxMonoidal.δ F _ _ ≫
    (_ ▷ F.obj (P.X i)) ≫ _ = _
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id]
  simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
  change F.map (λ_ (P.X i)).inv ≫ Functor.OplaxMonoidal.δ F _ _ ≫
    Functor.OplaxMonoidal.η F ▷ F.obj (P.X i) ≫ _ = _
  rw [← Functor.OplaxMonoidal.left_unitality_assoc]
  erw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

private theorem tensorUnit_complex_right
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, Limits.PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, Limits.PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive] (mF : F.CoreMonoidal) (P : CochainComplex C ℤ)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ 𝟙_ (CochainComplex C ℤ)) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ (F.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)))
    (hφ : ∀ n : ℤ, F.map (HomologicalComplex.ιTensorObj P (𝟙_ (CochainComplex C ℤ)) n 0 n
      (add_zero n)) ≫ φ.hom.f n =
      (mF.μIso (P.X n) ((𝟙_ (CochainComplex C ℤ)).X 0)).inv ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ((F.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex C ℤ))) n 0 n (add_zero n)) :
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    let u := (HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
    FC.map (ρ_ P).inv ≫ φ.hom ≫ FC.obj P ◁ u.inv = (ρ_ (FC.obj P)).inv := by
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let U : CochainComplex C ℤ := 𝟙_ _
  let u : 𝟙_ (CochainComplex D ℤ) ≅ FC.obj U :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
  have hu0 : u.inv.f 0 =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C)).hom ≫
        mF.εIso.inv ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ D)).inv := by
    simp [u, HomologicalComplex.single_map_f_self]
  let := mF.toMonoidal
  ext i : 1
  have h₁ : (ρ_ P).inv.f i = (HomologicalComplex.rightUnitor' P).inv i := rfl
  have h₂ : (ρ_ (FC.obj P)).inv.f i =
      (HomologicalComplex.rightUnitor' (FC.obj P)).inv i := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, h₁, h₂,
    HomologicalComplex.rightUnitor'_inv, HomologicalComplex.rightUnitor'_inv]
  change _ ≫ _ ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 (FC.obj P)) u.inv (curriedTensor _)
      (ComplexShape.up ℤ)).f i = _
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (hφ i)]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app,
    curriedTensor_obj_map, hu0]
  erw [MonoidalCategory.id_whiskerRight, Category.id_comp]
  change _ ≫ _ ≫ Functor.OplaxMonoidal.δ F _ _ ≫
    (F.obj (P.X i) ◁ _) ≫ _ = _
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, ← F.map_comp,
    Iso.inv_hom_id, F.map_id]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  change F.map (ρ_ (P.X i)).inv ≫ Functor.OplaxMonoidal.δ F _ _ ≫
    F.obj (P.X i) ◁ Functor.OplaxMonoidal.η F ≫ _ = _
  rw [← Functor.OplaxMonoidal.right_unitality_assoc]
  rfl


set_option maxHeartbeats 600000 in
-- The concrete sheaf tensor instances require extra elaboration heartbeats.
/-- The explicitly constructed unit comparison satisfies both unit laws on Q(P)
when P is K-flat. No statement about arbitrary derived objects is made here.
(Stacks, Tag 079U) -/
theorem derivedPullback_tensor_unit_kFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))]
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    : (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (λ_ ((derivedPullback g).obj A)).hom =
           η.hom ▷ (derivedPullback g).obj A ≫
             ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
             (derivedPullback g).map (λ_ A).hom) ∧
      (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (ρ_ ((derivedPullback g).obj A)).hom =
           (derivedPullback g).obj A ◁ η.hom ≫
             ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
             (derivedPullback g).map (ρ_ A).hom) := by
  let AX := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  let AT := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let U : CochainComplex AX ℤ := 𝟙_ _
  let u : 𝟙_ (CochainComplex AT ℤ) ≅ FC.obj U :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
  have huL := tensorUnit_complex_left F mF P (φ U P)
    (fun n ↦ hφ U P 0 n n (zero_add n))
  have huR := tensorUnit_complex_right F mF P (φ P U)
    (fun n ↦ hφ P U n 0 n (add_zero n))
  have hU : CochainComplex.IsKFlatTensor (R := X.sheaf) U := by
    intro N hN i
    exact (hN i).of_iso (ρ_ N).symm
  have hEP : IsIso (ε.app ((HomotopyCategory.quotient AX (ComplexShape.up ℤ)).obj P)) :=
    tensorUnit_counit_kFlat_isIso g F hF hmap ε hε P hP
  let QX := DerivedCategory.Q (C := AX)
  let QT := DerivedCategory.Q (C := AT)
  let η := derivedPullback_tensorUnitIso g F mF ε
  let e := fun K : CochainComplex AX ℤ ↦
    ε.app ((HomotopyCategory.quotient AX (ComplexShape.up ℤ)).obj K)
  obtain ⟨hQT, hη'⟩ := derivedPullback_tensorUnitIso_normalization g F mF ε
  have hη : η.inv = (derivedPullback g).map (Functor.LaxMonoidal.ε QX) ≫
      e U ≫ QT.map u.inv ≫ inv (Functor.LaxMonoidal.ε QT) := by
    apply (cancel_mono (Functor.LaxMonoidal.ε QT)).mp
    simpa only [cast_eq, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hη'
  have he : ∀ {K N : CochainComplex AX ℤ} (f : K ⟶ N),
      (derivedPullback g).map (QX.map f) ≫ e N = e K ≫ QT.map (FC.map f) := by
    intro K N f
    exact ε.naturality ((HomotopyCategory.quotient AX (ComplexShape.up ℤ)).map f)
  have hδ : ∀ K N : CochainComplex AX ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) K →
      CochainComplex.IsKFlatTensor (R := X.sheaf) N →
      ((μ.inv.app (QX.obj K)).app (QX.obj N)) ≫ (e K ⊗ₘ e N) ≫
        Functor.LaxMonoidal.μ QT (FC.obj K) (FC.obj N) =
      (derivedPullback g).map (Functor.LaxMonoidal.μ QX K N) ≫ e (K ⊗ N) ≫
        QT.map (φ K N).hom := by
    intro K N hK hN
    have hμ' := hμ K N hK hN
    simp only [cast_eq] at hμ'
    erw [← hμ']
    dsimp only [QX, QT, e]
    simp only [Iso.app_hom]
    rw [Iso.inv_hom_id_app_app_assoc]
    rfl
  have hl := tensorUnit_left_square QX QT FC (derivedPullback g) μ.inv e P u (φ U P)
    η hη (he (λ_ P).inv) (hδ U P hU hP) huL
  have hr := tensorUnit_right_square QX QT FC (derivedPullback g) μ.inv e P u (φ P U)
    η hη (he (ρ_ P).inv) (hδ P U hP hU) huR
  constructor
  · let a := λ_ ((derivedPullback g).obj (QX.obj P))
    let b := whiskerRightIso η ((derivedPullback g).obj (QX.obj P)) ≪≫
      (μ.app (𝟙_ (schemeDerivedCategory X))).app (QX.obj P) ≪≫
        (derivedPullback g).mapIso (λ_ (QX.obj P))
    have hab : a.symm = b.symm := by
      apply Iso.ext
      simpa only [a, b, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
        Iso.app_inv, whiskerRightIso, Category.assoc] using hl
    exact congrArg Iso.hom (Iso.symm_eq_iff.mp hab)
  · let a := ρ_ ((derivedPullback g).obj (QX.obj P))
    let b := whiskerLeftIso ((derivedPullback g).obj (QX.obj P)) η ≪≫
      (μ.app (QX.obj P)).app (𝟙_ (schemeDerivedCategory X)) ≪≫
        (derivedPullback g).mapIso (ρ_ (QX.obj P))
    have hab : a.symm = b.symm := by
      apply Iso.ext
      simpa only [a, b, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
        Iso.app_inv, whiskerLeftIso, Category.assoc] using hr
    exact congrArg Iso.hom (Iso.symm_eq_iff.mp hab)

end AlgebraicGeometry
