/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorSource
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorPresentationReduction

/-! # Realization of the finite-reduction reassociation square

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2.
(blueprint: lem-pur-finite-reduction-reassociation-intrinsic)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] finiteTensorPuritySourceComparison
  finiteReductionTensorInputComparison finiteTensorSourceModel finiteReductionTensorSourceComparison
private theorem reassociation_naturality (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (d : ℕ)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : M ⟶ N) :
    (P.compositionTwistShift X d).map a ≫ (P.smoothPurityReassociation X d N).hom =
      (P.smoothPurityReassociation X d M).hom ≫
        ((smoothPurityTensor P.Coefficient X).map a).app (P.diagonalTwist X d) := by
  have he (U) : P.smoothPurityReassociation X d U =
      smoothPurityTensorShiftGeneric
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
        (2 * (d : ℤ)) U (P.diagonalTwist X d) :=
    eq_of_heq (existsUnique_smoothPurityTensorShift
      (ModuleCat.{u + 1} P.Coefficient) X (2 * (d : ℤ)) U
      (P.diagonalTwist X d)).exists.choose_spec
  rw [he, he]
  dsimp only [smoothPurityTensorShiftGeneric, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    compositionTwistShift, Functor.comp_map]
  let T := curriedTensor (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
  have h := NatTrans.shift_app_comm (T.map a) (2 * (d : ℤ))
    ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧)
  apply (cancel_epi (((T.obj M).commShiftIso (2 * (d : ℤ))).hom.app
    ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))).1
  simp only [← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  change (T.map a).app _ ≫
      ((T.obj N).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
      ((T.obj N).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ _ =
    ((T.obj M).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
      ((T.obj M).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ _
  simp only [Iso.hom_inv_id_app_assoc]
  exact ((T.map a).naturality
    ((shiftFunctorCompIsoId _ (-(2 * (d : ℤ))) (2 * (d : ℤ))
      (neg_add_cancel _)).hom.app (P.diagonalTwist X d))).symm

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
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : M ⟶ N) :
    (P.compositionTwistShift X d).map a ≫ (P.finiteReductionFixedChart X d ζ hζ N).hom =
      (P.finiteReductionFixedChart X d ζ hζ M).hom ≫ a⟦2 * (d : ℤ)⟧' := by
  have he (U) := eq_of_heq
    (P.existsUnique_finiteReductionFixedChart X d ζ hζ U).choose_spec.1
  change ∀ U, P.finiteReductionFixedChart X d ζ hζ U = _ at he
  rw [he M, he N]
  dsimp only [finiteReductionChartComposite, Iso.trans_hom, Functor.mapIso_hom]
  change (P.compositionTwistShift X d).map a ≫
      (P.smoothPurityReassociation X d N).hom ≫ _ = _
  rw [← Category.assoc, reassociation_naturality]
  rw [Category.assoc, ← Category.assoc
    (((smoothPurityTensor P.Coefficient X).map a).app (P.diagonalTwist X d)),
    ← NatTrans.naturality]
  rw [Category.assoc, tensorUnit_naturality]
  simp only [Category.assoc, smoothPurityReassociation]

private def sourceChartNatIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.compositionShiftedPullback f d ≅
      P.finiteReductionPullback f ⋙ shiftFunctor _ (2 * (d : ℤ)) :=
  NatIso.ofComponents (P.finiteReductionSourceTrivialization f d ζ hζ) (by
    intro K L a
    let M := (P.smoothPurityPullback f).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map a)
    let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
    let E := (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory
    dsimp only [finiteReductionSourceTrivialization, Iso.trans_hom, Functor.mapIso_hom]
    dsimp only [compositionShiftedPullback, finiteReductionPullback, Functor.comp_map]
    simp only [Iso.app_hom, Category.assoc]
    erw [← Functor.map_comp_assoc, fixedChart_naturality,
      Functor.map_comp, Category.assoc]
    congr 1
    exact E.commShiftIso_hom_naturality M (2 * (d : ℤ)))

attribute [local irreducible] Scheme.sfIntrinsicDerivedEquivalence

private def pullbackReductionNatIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel f).symm
      (P.finiteReduction m hm hmn X) ≪≫
    (Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)

private theorem identify_chart_composite
    {C : Type*} [Category* C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : F ≅ E) (s : A ≅ F)
    (h : s.hom ≫ d.hom = a.hom ≫ b.hom ≫ c.hom) :
    (a ≪≫ b ≪≫ c ≪≫ d.symm).hom = s.hom := by
  apply (cancel_mono d.hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h.symm

@[irreducible] private def sourceReductionChartIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k) (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent) :
    P.compositionShiftedPullback f d ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).compositionShiftedPullback f d :=
  Functor.isoWhiskerRight (sourceChartNatIso P f d ζ hζ)
      (P.finiteReduction m hm hmn X) ≪≫
    Functor.associator (P.finiteReductionPullback f) (shiftFunctor _ (2 * (d : ℤ)))
      (P.finiteReduction m hm hmn X) ≪≫
    Functor.isoWhiskerLeft (P.finiteReductionPullback f)
      ((P.finiteReduction m hm hmn X).commShiftIso (2 * (d : ℤ))) ≪≫
    (Functor.associator (P.finiteReductionPullback f) (P.finiteReduction m hm hmn X)
      (shiftFunctor _ (2 * (d : ℤ)))).symm ≪≫
    Functor.isoWhiskerRight (pullbackReductionNatIso P m hm hmn f)
      (shiftFunctor _ (2 * (d : ℤ))) ≪≫
    Functor.associator (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionPullback f)
      (shiftFunctor _ (2 * (d : ℤ))) ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      (sourceChartNatIso (P.finiteReductionSetting m hm) f d η hη).symm

private theorem sourceReduction_naturality (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn X).map ((P.compositionShiftedPullback f d).map a) ≫
        (P.finiteReductionSourceComparison m hm hmn f d L).hom =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
          ((P.finiteReduction m hm hmn Y).map a) := by
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  let e := sourceReductionChartIso P m hm hmn f d ζ hζ η hη
  have he (U) : e.hom.app U = (P.finiteReductionSourceComparison m hm hmn f d U).hom := by
    have hs := (P.existsUnique_finiteReductionSourceComparison m hm hmn f d U).choose_spec.1
      ζ η hζ hη rfl
    change (P.finiteReductionSourceComparison m hm hmn f d U).hom ≫ _ = _ at hs
    dsimp only [e]
    unfold sourceReductionChartIso
    dsimp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, sourceChartNatIso, NatIso.ofComponents_hom_app,
      Iso.symm_hom, NatIso.ofComponents_inv_app, Functor.associator_hom_app,
      Functor.associator_inv_app]
    simp only [Category.id_comp]
    exact identify_chart_composite
      ((P.finiteReduction m hm hmn X).mapIso
        (P.finiteReductionSourceTrivialization f d ζ hζ U))
      (((P.finiteReduction m hm hmn X).commShiftIso (2 * (d : ℤ))).app
        ((P.finiteReductionPullback f).obj U))
      ((shiftFunctor _ (2 * (d : ℤ))).mapIso
        (P.finiteReductionPullbackComparison m hm hmn f U))
      ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η hη
        ((P.finiteReduction m hm hmn Y).obj U))
      (P.finiteReductionSourceComparison m hm hmn f d U) hs
  simpa only [Functor.comp_map, he] using e.hom.naturality a

private theorem preimage_input_triangle
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ D) (E' : C' ≌ D') (S : C ⥤ C') (R : D ⥤ D')
    (α : E.functor ⋙ R ≅ S ⋙ E'.functor) (K : D) :
    E'.inverse.map (α.hom.app (E.inverse.obj K)) ≫
        E'.unitInv.app (S.obj (E.inverse.obj K)) ≫
        (E'.functor.preimageIso
          (α.symm.app (E.inverse.obj K) ≪≫ R.mapIso (E.counitIso.app K) ≪≫
            (E'.counitIso.app (R.obj K)).symm)).hom =
      E'.inverse.map (R.map (E.counitIso.app K).hom) := by
  apply E'.functor.map_injective
  apply (cancel_mono (E'.counit.app (R.obj K))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← E'.counit_app_functor]
  erw [E'.counit_naturality_assoc]
  simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [Iso.inv_hom_id_app]
  change E'.counit.app (R.obj (E.functor.obj (E.inverse.obj K))) ≫
      R.map (E.counitIso.app K).hom ≫ 𝟙 (R.obj K) = _
  erw [Category.comp_id (R.map (E.counitIso.app K).hom)]
  simpa only [Iso.app_hom, Functor.comp_obj, Functor.id_obj] using
    (E'.counit_naturality (R.map (E.counitIso.app K).hom)).symm

private theorem realize_preimage_composite {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} {U V W Z : D}
    (α : U ≅ F.obj A) (b : U ≅ V) (c : V ≅ W) (e : W ≅ Z)
    (h : Z ≅ F.obj B) :
    α.hom ≫ F.map (F.preimageIso (((α.symm ≪≫ b) ≪≫ (c ≪≫ e)) ≪≫ h)).hom =
      b.hom ≫ c.hom ≫ e.hom ≫ h.hom := by
  simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem paste_source_transport
    {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {M N : C} (t : M ≅ N) {A B I J Z : D}
    (α : R.obj N ⟶ A) (s : A ⟶ B) (x : B ⟶ Z)
    (c : R.obj M ⟶ I) (v : I ⟶ J) (w : J ⟶ B)
    (z : I ⟶ Z) (k : R.obj N ⟶ Z) (q : M ⟶ N) (ht : t.hom = q)
    (hs : α ≫ s = R.map t.inv ≫ c ≫ v ≫ w)
    (hi : v ≫ w ≫ x = z) (hn : R.map q ≫ k = c ≫ z) :
    α ≫ s ≫ x = k := by
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [hi, ← hn, ← ht, ← Category.assoc, ← R.map_comp, Iso.inv_hom_id,
    R.map_id, Category.id_comp]

private theorem transport_source_generic
    {C D C' D' B A' B' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    [Category* B] [Category* A'] [Category* B']
    (E : C ≌ D) (E' : C' ≌ D') (J : A' ≌ B')
    (F : C ⥤ B) (H : C' ⥤ A') (RX : B ⥤ B') (RY : D ⥤ D') (S : C ⥤ C')
    (α : E.functor ⋙ RY ≅ S ⋙ E'.functor)
    (c : ∀ K : D, RX.obj (F.obj (E.inverse.obj K)) ≅
      (H ⋙ J.functor).obj (E'.inverse.obj (RY.obj K)))
    (K : D) {A : A'} (a : RX.obj (F.obj (E.inverse.obj K)) ≅ J.functor.obj A)
    (hn : RX.map ((E.inverse ⋙ F).map (E.counitIso.app K).hom) ≫ (c K).hom =
      (c (E.functor.obj (E.inverse.obj K))).hom ≫
        (E'.inverse ⋙ H ⋙ J.functor).map (RY.map (E.counitIso.app K).hom)) :
    a.hom ≫ J.functor.map
        (J.functor.preimageIso
          (((a.symm ≪≫ (RX.mapIso
              (F.mapIso (E.unitIso.symm.app (E.inverse.obj K)))).symm) ≪≫
            (c (E.functor.obj (E.inverse.obj K)) ≪≫
              (E'.inverse ⋙ H ⋙ J.functor).mapIso (α.app (E.inverse.obj K)))) ≪≫
            (H ⋙ J.functor).mapIso (E'.unitIso.symm.app
              (S.obj (E.inverse.obj K))))).hom ≫
      (H ⋙ J.functor).map
        (E'.functor.preimageIso
          (α.symm.app (E.inverse.obj K) ≪≫ RY.mapIso (E.counitIso.app K) ≪≫
            (E'.counitIso.app (RY.obj K)).symm)).hom = (c K).hom := by
  let L := E.inverse.obj K
  let G := H ⋙ J.functor
  refine paste_source_transport RX (F.mapIso (E.unitIso.symm.app L)) a.hom _ _
    (c (E.functor.obj L)).hom ((E'.inverse ⋙ G).map (α.hom.app L))
    (G.map (E'.unitIso.symm.app (S.obj L)).hom) _ (c K).hom
    ((E.inverse ⋙ F).map (E.counitIso.app K).hom) ?_ ?_ ?_ hn
  · simpa only [Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Functor.comp_map,
      Iso.app_hom] using congrArg F.map (E.unitInv_app_inverse K)
  · exact realize_preimage_composite J.functor a
      (RX.mapIso (F.mapIso (E.unitIso.symm.app L))).symm
      (c (E.functor.obj L)) ((E'.inverse ⋙ G).mapIso (α.app L))
      (G.mapIso (E'.unitIso.symm.app (S.obj L)))
  · have h := congrArg G.map (preimage_input_triangle E E' S RY α K)
    simpa only [G, L, Functor.map_comp, Functor.comp_map, Functor.comp_obj,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] using h

private theorem source_transport (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    let Q := P.finiteReductionSetting m hm
    let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
    let E' := Scheme.sfIntrinsicDerivedEquivalence X Q.Ring
    let α := ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X
    α.hom.app ((P.compositionTwistShift X d).obj
        ((P.smoothPurityPullback f).obj (E.inverse.obj K))) ≫
      E'.functor.map (P.finiteTensorPuritySourceComparison m hm hmn f d
        (E.inverse.obj K)).hom ≫
      E'.functor.map ((Q.compositionTwistShift X d).map
        ((Q.smoothPurityPullback f).map
          (P.finiteReductionTensorInputComparison m hm hmn Y K).hom)) =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom := by
  unfold finiteTensorPuritySourceComparison finiteTensorSourceModel
    finiteReductionTensorInputComparison
  have h := transport_source_generic
    (A := (P.finiteTensorReduction m hm hmn X).obj
      ((P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))))
    (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring)
    (Scheme.sfIntrinsicDerivedEquivalence Y (P.finiteReductionSetting m hm).Ring)
    (Scheme.sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring)
    (P.smoothPurityPullback f ⋙ P.compositionTwistShift X d ⋙
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor)
    ((P.finiteReductionSetting m hm).smoothPurityPullback f ⋙
      (P.finiteReductionSetting m hm).compositionTwistShift X d)
    (P.finiteReduction m hm hmn X) (P.finiteReduction m hm hmn Y)
    (P.finiteTensorReduction m hm hmn Y)
    (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y)
    (P.finiteReductionSourceComparison m hm hmn f d) K
    ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X).app
        ((P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))))
    (sourceReduction_naturality P m hm hmn f d
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).counitIso.app K).hom)
  exact h

private theorem paste_reassociation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (R : C ⥤ E) (S : C ⥤ D) (F : D ⥤ E)
    (α : R ≅ S ⋙ F) {A B : C} {U V W Z : D}
    (τ : A ⟶ B) (s : S.obj A ⟶ U) (t : S.obj B ⟶ V)
    (τ' : U ⟶ V) (a : U ⟶ W) (b : V ⟶ Z) (τ'' : W ⟶ Z)
    (c : R.obj A ⟶ F.obj W)
    (hs : S.map τ ≫ t = s ≫ τ') (hn : τ' ≫ b = a ≫ τ'')
    (hc : α.hom.app A ≫ F.map s ≫ F.map a = c) :
    R.map τ ≫ (α.hom.app B ≫ F.map t ≫ F.map b) = c ≫ F.map τ'' := by
  rw [α.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← F.map_comp_assoc, hs, F.map_comp]
  simp only [Category.assoc]
  rw [← F.map_comp, hn, F.map_comp]
  rw [← Category.assoc, ← Category.assoc, Category.assoc (α.hom.app A), hc]

set_option linter.unusedSectionVars false
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The reassociation factor reduces through the independently constructed tensor source.
Source: blueprint reduction Step 2, twist/shift comparison
(blueprint: lem-pur-finite-reduction-reassociation-intrinsic).
Proof: put L equal to the inverse intrinsic realization of K. Apply
finite_tensor_presentation_reduction to L. Apply the smaller-level realization
functor to its equality and conjugate by scalarPresentation. Its naturality at
the reassociation identifies the left side with reduction of the realized tau.
Expand finiteTensorPuritySourceComparison: the scalar presentation and realization
units give exactly finiteReductionSourceComparison at the realized L. Naturality
in the canonical counit E(E.inverse K) -> K then changes that input to K.
The input comparison is finiteReductionTensorInputComparison, so naturality of
pullback, tensor and the second-factor shift gives precisely the displayed target.
The tensor-source comparison uses only scalar balancing, pullback and the positive
line; no purity map or diagonal orientation enters this assertion. -/
theorem finiteReduction_reassociation (d : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    [SmoothOfRelativeDimension d f] :
    (P.finiteReduction m hm hmn X).map
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).hom) ≫
      (P.finiteReductionTensorSourceComparison m hm hmn f d K).hom =
    (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
      (Scheme.sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.map
        ((P.finiteReductionSetting m hm).smoothPurityReassociation X d
          (((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Y
              (P.finiteReductionSetting m hm).Ring).inverse.obj
                ((P.finiteReduction m hm hmn Y).obj K)))).hom := by
  unfold finiteReductionTensorSourceComparison
  dsimp only [Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  let Q := P.finiteReductionSetting m hm
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let E' := Scheme.sfIntrinsicDerivedEquivalence X Q.Ring
  let L := E.inverse.obj K
  let S := P.finiteTensorReduction m hm hmn X
  let α := ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
    (P.finiteReductionRingHom m hm hmn) X
  have : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos Y).IsClosedUnderIsomorphisms :=
    Scheme.finiteTorsionConstructible_isClosedUnderIsomorphisms P.field P.coefficients.l
      P.coefficients.different P.extension P.level P.level_pos Y
  have hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      (E.functor.obj L) := by
    refine ⟨ObjectProperty.prop_of_iso _ (E.counitIso.app K).symm hK.1, ?_⟩
    obtain ⟨a, b, hab, ht⟩ := hK.2
    refine ⟨a, b, hab, ?_⟩
    intro M N hM g hg hN T i hi
    exact ht M N (hM.map (fun e ↦ e ≪≫ E.counitIso.app K)) g hg hN T i hi
  exact paste_reassociation
    ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor ⋙
      P.finiteReduction m hm hmn X) S E'.functor α
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj L)).hom
    (P.finiteTensorPuritySourceComparison m hm hmn f d L).hom
    (P.finiteTensorPurityTargetComparison m hm hmn f d L).hom
    (Q.smoothPurityReassociation X d
      ((Q.smoothPurityPullback f).obj ((P.finiteTensorReduction m hm hmn Y).obj L))).hom
    ((Q.compositionTwistShift X d).map ((Q.smoothPurityPullback f).map
      (P.finiteReductionTensorInputComparison m hm hmn Y K).hom))
    (((smoothPurityTensor Q.Coefficient X).map
      ((Q.smoothPurityPullback f).map
        (P.finiteReductionTensorInputComparison m hm hmn Y K).hom)).app (Q.diagonalTwist X d))
    (Q.smoothPurityReassociation X d ((Q.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj
        ((P.finiteReduction m hm hmn Y).obj K)))).hom
    (P.finiteReductionSourceComparison m hm hmn f d K).hom
    (P.finite_tensor_presentation_reduction m hm hmn f d L hL)
    (reassociation_naturality Q X d ((Q.smoothPurityPullback f).map
      (P.finiteReductionTensorInputComparison m hm hmn Y K).hom)).symm
    (source_transport P m hm hmn f d K)

end Morphism
end WeilConjectures.PurityFiniteSetting
