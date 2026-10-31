/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem tensorShiftGeneric_naturality
    (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) {M N : _root_.DerivedCategory C} (a : M ⟶ N)
    (T : _root_.DerivedCategory C) :
    (smoothPurityTensorShiftGeneric C r M T).hom ≫
        ((curriedTensor (_root_.DerivedCategory C)).map a).app T =
      (shiftFunctor _ r).map
          (((curriedTensor (_root_.DerivedCategory C)).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShiftGeneric C r N T).hom := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have h := NatTrans.shift_app_comm (F.map a) r (T⟦-r⟧)
  have hi : ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.map a).app ((T⟦-r⟧)⟦r⟧) =
      (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
        ((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) := by
    rw [← cancel_mono (((F.obj N).commShiftIso r).hom.app (T⟦-r⟧))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  change (((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.obj M).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) ≫
        (F.map a).app T =
    (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
      (((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) ≫
        (F.obj N).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T))
  have hn := (F.map a).naturality
    ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)
  calc
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg
      (fun z ↦ ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫ z) hn
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun z ↦ z ≫ (F.obj N).map
        ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) hi
    _ = _ := Category.assoc _ _ _

/-- The specified tensor-shift comparison commutes with maps in its first factor.
Source: the canonical bifunctor shift structure, as used in step 2 of
`prop-pur-smooth-purity-naturality-cover`. -/
private theorem smoothPurityTensorShift_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (r : ℤ)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N)
    (T : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensorShift A X r M T).hom ≫
        ((smoothPurityTensor A X).map a).app T =
      (shiftFunctor _ r).map (((smoothPurityTensor A X).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShift A X r N T).hom := by
  have hM := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r M T).exists
    |>.choose_spec
  have hN := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r N T).exists
    |>.choose_spec
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold smoothPurityTensorShift smoothPurityTensorShiftCoefficients
  rw [eM, eN]
  exact tensorShiftGeneric_naturality _ r a T

@[irreducible] private def tensorRightIso {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    {N N' : C} (b : N ≅ N') : T.flip.obj N ≅ T.flip.obj N' :=
  NatIso.ofComponents (fun M ↦ (T.obj M).mapIso b)
    (fun a ↦ ((T.map a).naturality b.hom).symm)

set_option maxHeartbeats 2000000 in
-- The eight canonical component types require additional definitional reduction.
end WeilConjectures.PurityFiniteSetting
