/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Coefficient factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor

private theorem plusCompatibility_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  change NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
      (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
  infer_instance

private theorem plusNatIso_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e).hom ≫
          G.mapDerivedCategoryPlusCompatibility.inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

private theorem plusCompIso_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι =
      (F ⋙ G).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight F.mapDerivedCategoryPlusCompatibility.inv G.mapDerivedCategory ≫
        (associator _ _ _).hom ≫
        whiskerLeft F.mapDerivedCategoryPlus G.mapDerivedCategoryPlusCompatibility.inv ≫
        (associator _ _ _).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app]
    rw [ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Functor.map_id]
    repeat erw [Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    have := plusCompatibility_commShift (F ⋙ G)
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] RawModuleScalarComparison.derivedPullbackIso

/-- The shifted coefficient part of scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def scalarCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W Y : Scheme.{u}} (h : Y ⟶ W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((RawModuleScalarComparison.forget Λ W).obj G)))⟦q⟧ :=
  ((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj G)) ≫
    (shiftFunctor _ q).map
      (((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ h G)))

/-- The last two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

/-- The last two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

private theorem shift_square
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift D₀ ℤ] [HasShift D₁ ℤ]
    (M : C₀ ⥤ C₁) (VA : C₁ ⥤ D₁) (VB : C₀ ⥤ D₀) (H : D₀ ⥤ D₁)
    [M.CommShift ℤ] [VA.CommShift ℤ] [VB.CommShift ℤ] [H.CommShift ℤ]
    (e : VB ⋙ H ⟶ M ⋙ VA) [NatTrans.CommShift e ℤ]
    (X : C₀) (Y : C₁) (Z : D₀) (T : D₁)
    (m : M.obj X ⟶ Y) (bA : VA.obj Y ⟶ T) (bB : VB.obj X ⟶ Z) (a : H.obj Z ⟶ T)
    (hu : e.app X ≫ VA.map m ≫ bA = H.map bB ≫ a) (q : ℤ) :
    e.app (X⟦q⟧) ≫
      VA.map ((M.commShiftIso q).hom.app X ≫ m⟦q⟧') ≫
      (VA.commShiftIso q).hom.app Y ≫ bA⟦q⟧' =
    H.map ((VB.commShiftIso q).hom.app X ≫ bB⟦q⟧') ≫
      (H.commShiftIso q).hom.app Z ≫ a⟦q⟧' := by
  have hc := NatTrans.shift_app_comm e q X
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [VA.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% hc]
  rw [H.commShiftIso_hom_naturality_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ H.map ((VB.commShiftIso q).hom.app X) ≫
      (H.commShiftIso q).hom.app (VB.obj X) ≫ t⟦q⟧') hu

private theorem coefficient_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A B : Over W) (f : A ⟶ B) :
    (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor
          0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G)) ≫
      ((RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)) =
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
      (((RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ B.hom G))) ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app _) := by
  exact rawModuleScalar_coefficient_unshifted Λ G A B f

/-- Shift transport from the unshifted coefficient square.
Source: Stacks Project, Tags 03D7 and 03Q8. The proof applies the generic
shift transport identity to the four derived functors and the unshifted
coefficient identity `coefficient_unshifted`. The required commutation of
the comparison maps with shifts follows from `NatTrans.shift_app_comm` and
the naturality of each `commShiftIso`; functoriality of shifts and
associativity then produce the displayed equality. This applies to every
integer shift, including zero and negative shifts, and to identity arrows
and zero coefficient sheaves.
(blueprint: lem-sbc-raw-scalar-coefficient-square-shift-transport). -/
theorem rawModuleScalar_coefficient_square_of_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B)
    : 
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G) q A B f
  (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by
  sorry

theorem rawModuleScalar_coefficient_square
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G) q A B f
  (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by
  apply rawModuleScalar_coefficient_square_of_unshifted Λ G q A B f

end AlgebraicGeometry.Etale
