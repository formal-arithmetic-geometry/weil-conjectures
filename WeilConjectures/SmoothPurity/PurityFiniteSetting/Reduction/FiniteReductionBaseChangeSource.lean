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

private theorem sourceChart_naturality (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring} (a : K ⟶ L) :
    (P.compositionShiftedPullback f d).map a ≫
        (P.finiteReductionSourceTrivialization f d ζ hζ L).hom =
      (P.finiteReductionSourceTrivialization f d ζ hζ K).hom ≫
        ((P.finiteReductionPullback f).map a)⟦2 * (d : ℤ)⟧' := by
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  let E := (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory
  let b := (P.smoothPurityPullback f).map
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map a)
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let N := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj L)
  change E.map ((P.compositionTwistShift X d).map b) ≫
      (E.map (P.finiteReductionFixedChart X d ζ hζ N).hom ≫
        (E.commShiftIso (2 * (d : ℤ))).hom.app N) =
    (E.map (P.finiteReductionFixedChart X d ζ hζ M).hom ≫
        (E.commShiftIso (2 * (d : ℤ))).hom.app M) ≫
      (E.map b)⟦2 * (d : ℤ)⟧'
  have he := congrArg E.map (fixedChart_naturality P X d ζ hζ b)
  simp only [Functor.map_comp] at he
  rw [← Category.assoc, he, Category.assoc, Functor.commShiftIso_hom_naturality,
    Category.assoc]

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

private theorem baseChangeSource_chart (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
      (P.finiteReductionSourceTrivialization f' d ζ hζ
        ((P.finiteReductionPullback v).obj K)).hom =
    (P.finiteReductionPullback u).map
        (P.finiteReductionSourceTrivialization f d ζ hζ K).hom ≫
      ((P.finiteReductionPullback u).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
      (P.finiteReductionPullbackSquare u f' f v sq K).hom⟦2 * (d : ℤ)⟧' := by
  rw [finiteReductionBaseChangeSource,
    (P.existsUnique_finiteReductionBaseChangeSource u f' f v sq d K).choose_spec.1 ζ hζ]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The root-normalized source arrow commutes with the actual quotient comparisons.
Source: thm-pur-finite-reduction-of-purity, proof Steps 2 and 4, source part of base change
(blueprint: lem-pur-finite-reduction-base-change-source).
Proof: choose a primitive ell^n root and its ell^(n-m) power at level m. Expand each
source comparison using its characterization in these compatible charts, and expand
the base-change source using its characterization in the same root chart. Naturality
moves the chart maps through scalar extension and inverse image. The scalar/pullback
mate commutes with the two pullback compositors: transpose this equation to the
restriction square, where it is the ordinary inverse-image compositor equation.
The exact shift comparisons commute with this mate, since scalar extension's shift
is the mate of the termwise shift on restriction. The intervening chart maps cancel,
leaving the displayed equation. Changing roots rescales both sides by the same unit.
This works for arbitrary K and arbitrary base morphism v; no exceptional inverse
image, purity map, or flatness of the quotient is used. For d=0 the root charts are
the tensor-unit charts, and the same argument is the ordinary pullback square. -/
theorem finiteReduction_baseChangeSource
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).compositionShiftedPullback f' d).map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionShiftedPullback f d).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionBaseChangeSource
        u f' f v sq d ((P.finiteReduction m hm hmn Y).obj K)).hom) := by
  classical
  let Q := P.finiteReductionSetting m hm
  let R := P.finiteReduction m hm hmn
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  have : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η Q.diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  have hs (T U : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
      (a : T ⟶ U) (M : Scheme.proEtaleDerivedCategory U P.Ring) :
      (P.finiteReductionSourceComparison m hm hmn a d M).hom ≫
        (Q.finiteReductionSourceTrivialization a d η hη ((R U).obj M)).hom =
      (R T).map (P.finiteReductionSourceTrivialization a d ζ hζ M).hom ≫
        ((R T).commShiftIso (2 * (d : ℤ))).hom.app
          ((P.finiteReductionPullback a).obj M) ≫
        (P.finiteReductionPullbackComparison m hm hmn a M).hom⟦2 * (d : ℤ)⟧' :=
    (P.existsUnique_finiteReductionSourceComparison m hm hmn a d M).choose_spec.1
      ζ η hζ hη rfl
  have hb := baseChangeSource_chart P u f' f v sq d K ζ hζ
  have hbQ := baseChangeSource_chart Q u f' f v sq d ((R Y).obj K) η hη
  have hn := sourceChart_naturality Q f' d η hη
    (P.finiteReductionPullbackComparison m hm hmn v K).hom
  have hp := pullbackComparison_naturality P m hm hmn u
    (P.finiteReductionSourceTrivialization f d ζ hζ K).hom
  have hc := P.finiteReduction_shiftedPullbackCube m hm hmn u f' f v sq
    (2 * (d : ℤ)) K
  apply (cancel_mono (Q.finiteReductionSourceTrivialization f' d η hη
    ((Q.finiteReductionPullback v).obj ((R Y).obj K))).hom).1
  simp only [Category.assoc]
  rw [hn, ← Category.assoc
    (P.finiteReductionSourceComparison m hm hmn f' d
      ((P.finiteReductionPullback v).obj K)).hom, hs]
  simp only [Category.assoc]
  rw [← (R X').map_comp_assoc, hb, Functor.map_comp]
  rw [hbQ]
  simp only [Category.assoc]
  rw [← (Q.finiteReductionPullback u).map_comp_assoc, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    (P.finiteReductionPullbackComparison m hm hmn u
      ((P.compositionShiftedPullback f d).obj K)).hom, ← hp]
  simp only [Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ (R X').map ((P.finiteReductionPullback u).map
      (P.finiteReductionSourceTrivialization f d ζ hζ K).hom) ≫ z) hc

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
