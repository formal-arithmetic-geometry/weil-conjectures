/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
import all WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Unit evaluation of the exceptional tensor mate

Source: smooth-purity model paragraph and projection-purity-agreement normalization.
(blueprint: lem-route-smooth-purity-theta-unit).
-/

noncomputable section
set_option autoImplicit false
universe u c d e h
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

section Generic
variable {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private theorem single_unit_inv :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).inv = 𝟙 _ := by
  have h₁ : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (HomotopyCategory.quotient C (.up ℤ)) = 𝟙 _ := rfl
  have h₃ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  simp only [_root_.DerivedCategory.singleFunctorObjUnitIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom, Functor.Monoidal.εIso_hom, Iso.app_inv,
    h₁, h₂, h₃, _root_.DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app]
  erw [(_root_.DerivedCategory.Qh (C := C)).map_id, Category.comp_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem single_unit_hom :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom = 𝟙 _ := by
  have h := (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom_inv_id
  rw [single_unit_inv] at h
  exact (Category.comp_id _).symm.trans h
end Generic

section Generic
variable {C : Type c} [Category C] [Abelian C] [HasDerivedCategory C]
  {D : Type d} [Category D] [Abelian D] [HasDerivedCategory D]
  {E : Type e} [Category E] [Abelian E] [HasDerivedCategory E]
  {H : Type h} [Category H] [Abelian H] [HasDerivedCategory H]
  (F : C ⥤ D) (G : D ⥤ E) (J : C ⥤ H) (I : H ⥤ E)
  [F.Additive] [G.Additive] [J.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem square_single (s : F ⋙ G ≅ J ⋙ I) (V : C) :
    (((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      Functor.mapDerivedCategoryCompIso J I).hom.app
        ((_root_.DerivedCategory.singleFunctor C 0).obj V)) ≫
      I.mapDerivedCategory.map ((J.mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (J.obj V) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj V) ≫
      (_root_.DerivedCategory.singleFunctor E 0).map (s.hom.app V) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G V]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

end Generic

@[expose] public section

set_option maxHeartbeats 1000000 in
-- Normalize the large exact-derived pullback and tensor comparison composites.
end

end WeilConjectures.PurityFiniteSetting
