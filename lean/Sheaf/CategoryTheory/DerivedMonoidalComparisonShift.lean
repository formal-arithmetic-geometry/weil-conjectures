/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal

/-!
# Shift and unit compatibility of the canonical derived tensor comparison

Source: the monoidal localization construction of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison` and the
flat-resolution shift argument of `UpperStarMonoidal.Shift`.
(blueprint: lem-sf-derived-monoidal-comparison-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor
namespace GenericDerivedTensorShift
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ]

local instance leftDerivedDerivedTensorCommShift (K : DerivedCategory C) :
    (F.leftDerivedDerivedTensor.obj K).CommShift ℤ :=
  inferInstanceAs (((curriedTensor _).obj K ⋙ F.leftDerivedFunctor).CommShift ℤ)

local instance derivedTensorLeftDerivedCommShift (K : DerivedCategory C) :
    (F.derivedTensorLeftDerived.obj K).CommShift ℤ :=
  inferInstanceAs ((F.leftDerivedFunctor ⋙
    (curriedTensor _).obj (F.leftDerivedFunctor.obj K)).CommShift ℤ)

private theorem commShift_Qh (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X)
    (hFX : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomotopyCategory (.up ℤ)).obj X)) :
    NatTrans.CommShift
      (F₁ := (curriedTensor (DerivedCategory C)).obj (Qh.obj X) ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ (curriedTensor (DerivedCategory D)).obj
        (F.leftDerivedFunctor.obj (Qh.obj X)))
      (F.leftDerivedTensorComparison.app (Qh.obj X)) ℤ := by
  apply DerivedCategory.commShift_of_tensorLeft_fac F F.leftDerivedFunctor
    F.leftDerivedFunctorCounit X hX hFX
  intro M
  have h := F.leftDerivedTensorComparison_app_app_comp_counit X M
  simp only [tensorLeftCounit, Functor.bifunctorCounit₁_app,
    curriedTensor_map_app, curriedTensor_obj_map,
    Functor.derivedTensorLeftDerivedCounit, NatTrans.comp_app,
    Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
    Functor.LaxMonoidal.μNatTrans_app_app, Functor.leftDerivedDerivedTensorCounit,
    Functor.postcompose₂_map_app_app_app, Functor.postcompose₂_obj_map_app_app,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.postcompose₂_obj_obj_obj_obj,
    curriedTensor_obj_obj, Category.assoc] at h ⊢
  exact h

omit [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
private theorem commShift_of_iso {K K' : DerivedCategory C} (e : K ≅ K')
    [NatTrans.CommShift (F₁ := (curriedTensor _).obj K' ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ (curriedTensor _).obj (F.leftDerivedFunctor.obj K'))
      (F.leftDerivedTensorComparison.app K') ℤ] :
    NatTrans.CommShift (F₁ := (curriedTensor _).obj K ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ (curriedTensor _).obj (F.leftDerivedFunctor.obj K))
      (F.leftDerivedTensorComparison.app K) ℤ := by
  have eq : F.leftDerivedTensorComparison.app K =
      Functor.whiskerRight ((curriedTensor _).map e.hom) F.leftDerivedFunctor ≫
        F.leftDerivedTensorComparison.app K' ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) := by
    let α := F.leftDerivedTensorComparison
    change α.app K = F.leftDerivedDerivedTensor.map e.hom ≫ α.app K' ≫
      F.derivedTensorLeftDerived.map e.inv
    rw [← Category.assoc, α.naturality, Category.assoc, ← Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map e.hom) ℤ)
  have : NatTrans.CommShift
      ((curriedTensor (DerivedCategory D)).map (F.leftDerivedFunctor.map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift
      ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) ℤ)
  have h₁ : NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor (DerivedCategory C)).map e.hom)
        F.leftDerivedFunctor) ℤ := inferInstance
  have h₂ : NatTrans.CommShift
      (Functor.whiskerLeft F.leftDerivedFunctor
        ((curriedTensor (DerivedCategory D)).map (F.leftDerivedFunctor.map e.inv))) ℤ :=
    inferInstance
  have hmid : NatTrans.CommShift
      (F.leftDerivedTensorComparison.app K') ℤ := inferInstance
  rw [eq]
  infer_instance

/-- The canonical tensor comparison of a derived exact monoidal functor commutes with shifts.
The comparison is computed on flat resolutions, where this is the shift compatibility of
ordinary tensor products, and then transported across the resolution isomorphism. -/
theorem commShift (K : DerivedCategory C) :
    NatTrans.CommShift (F₁ := (curriedTensor _).obj K ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ (curriedTensor _).obj (F.leftDerivedFunctor.obj K))
      (F.leftDerivedTensorComparison.app K) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hFR := F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ K₀
  have := commShift_Qh F ((HomotopyCategory.quotient _ _).obj R)
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hFR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_of_iso F e

omit [HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
theorem exists_kFlatMap_iso (K : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ K) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage K)
  have : IsIso (Qh.map R.w) :=
    Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso K⟩⟩

/-- The canonical tensor comparison, with its induced unit, is oplax monoidal. -/
@[instance_reducible]
noncomputable def oplaxMonoidal : F.leftDerivedFunctor.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  Functor.OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    (F.leftDerivedTensorComparison_app_app_comp_tensorHom) F.kFlatMap
    (exists_kFlatMap_iso F)
    (fun x _ hb ↦ Functor.isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

omit [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
/-- The unit of the derived oplax monoidal functor is invertible. -/
theorem isIso_unit :
    letI := oplaxMonoidal F
    IsIso (Functor.OplaxMonoidal.η F.leftDerivedFunctor) := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map (Functor.LaxMonoidal.ε Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
      CategoryTheory.inv (Functor.LaxMonoidal.ε Qh)))

end GenericDerivedTensorShift
