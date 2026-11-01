/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionShiftedPullbackCube
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Reduction of the source arrow in the smooth base-change square

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, proof Steps 2 and 4.
(blueprint: lem-pur-finite-reduction-base-change-source)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
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

private theorem tensorUnitGeneric_naturality
    (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    {M N : _root_.DerivedCategory C} (a : M ⟶ N) (r : ℤ) :
    ((curriedTensor (_root_.DerivedCategory C)).map a).app
        ((𝟙_ (_root_.DerivedCategory C))⟦r⟧) ≫
      (finiteReductionTensorUnitGeneric C N r).hom =
    (finiteReductionTensorUnitGeneric C M r).hom ≫ a⟦r⟧' := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have hs := NatTrans.shift_app_comm (F.map a) r (𝟙_ (_root_.DerivedCategory C))
  dsimp only [finiteReductionTensorUnitGeneric, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← hs, Category.assoc, ← (shiftFunctor _ r).map_comp]
  have hn : (F.map a).app (𝟙_ (_root_.DerivedCategory C)) ≫ (ρ_ N).hom =
      (ρ_ M).hom ≫ a := MonoidalCategory.rightUnitor_naturality a
  rw [hn, Functor.map_comp, Category.assoc]

private theorem tensorUnit_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) (r : ℤ) :
    ((smoothPurityTensor A X).map a).app
        ((𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))⟦r⟧) ≫
      (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X N r).hom =
    (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X M r).hom ≫ a⟦r⟧' := by
  have hM := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X M r).choose_spec.1
  have hN := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X N r).choose_spec.1
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold finiteReductionTensorUnit
  rw [eM, eN]
  exact tensorUnitGeneric_naturality _ a r

private theorem fixedChart_naturality (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : M ⟶ N) :
    (P.compositionTwistShift X d).map a ≫ (P.finiteReductionFixedChart X d ζ hζ N).hom =
      (P.finiteReductionFixedChart X d ζ hζ M).hom ≫ a⟦2 * (d : ℤ)⟧' := by
  have hM := (P.existsUnique_finiteReductionFixedChart X d ζ hζ M).choose_spec.1
  have hN := (P.existsUnique_finiteReductionFixedChart X d ζ hζ N).choose_spec.1
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold finiteReductionFixedChart
  rw [eM, eN]
  dsimp only [finiteReductionChartComposite, compositionTwistShift, Functor.comp_map,
    Functor.flip_obj_map, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc,
    ← smoothPurityTensorShift_naturality P.Coefficient X (2 * (d : ℤ)) a]
  rw [Category.assoc, ← Category.assoc
    (((smoothPurityTensor P.Coefficient X).map a).app (P.diagonalTwist X d)),
    ← NatTrans.naturality]
  rw [Category.assoc, tensorUnit_naturality]
  simp only [Category.assoc]

private theorem pullbackComparison_naturality (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {S T : Scheme.{u}} (v : S ⟶ T)
    {K L : Scheme.proEtaleDerivedCategory T P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn S).map ((P.finiteReductionPullback v).map a) ≫
        (P.finiteReductionPullbackComparison m hm hmn v L).hom =
      (P.finiteReductionPullbackComparison m hm hmn v K).hom ≫
        ((P.finiteReductionSetting m hm).finiteReductionPullback v).map
          ((P.finiteReduction m hm hmn T).map a) := by
  let e := Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel v).symm
      (P.finiteReduction m hm hmn S) ≪≫
    (Scheme.proEtaleReductionPullbackIso v
      (Scheme.proEtaleConstantRing T P.Ring)
      (Scheme.proEtaleConstantRing T (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing S P.Ring)
      (Scheme.proEtaleConstantRing S (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := S) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison v P.Ring)
      (Scheme.proEtaleConstantRingComparison v (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn v)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn T)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel v)
  simpa only [e, finiteReductionPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom, Iso.app_inv,
    Functor.comp_map, Functor.mapIso_hom, Functor.mapIso_inv] using e.hom.naturality a

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [IsSeparated (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

set_option linter.unusedSectionVars false in
end WeilConjectures.PurityFiniteSetting
