/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularMultiplication
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Regular coefficient multiplication and the normalized unit coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
private theorem multiplication_model_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (QY : C ⥤ C') (QX : D ⥤ D') (L : C ⥤ D) (H : C' ⥤ D')
    (factor : QY ⋙ H ≅ L ⋙ QX)
    (TY : C × C ⥤ C) (TX : D × D ⥤ D)
    (SY : C' × C' ⥤ C') (SX : D' × D' ⥤ D')
    (μ : SY ⋙ H ≅ (H.prod H) ⋙ SX)
    (OY : C) (OX : D)
    (iY : QY.obj (TY.obj (OY, OY)) ≅ SY.obj (QY.obj OY, QY.obj OY))
    (iF : QX.obj (TX.obj (L.obj OY, L.obj OY)) ≅
      SX.obj (QX.obj (L.obj OY), QX.obj (L.obj OY)))
    (iX : QX.obj (TX.obj (OX, OX)) ≅ SX.obj (QX.obj OX, QX.obj OX))
    (a : L.obj OY ≅ OX) (mY : TY.obj (OY, OY) ⟶ OY) (mX : TX.obj (OX, OX) ⟶ OX)
    (c : L.obj (TY.obj (OY, OY)) ⟶ TX.obj (L.obj OY, L.obj OY))
    (hμ : H.map iY.hom ≫ μ.hom.app (QY.obj OY, QY.obj OY) ≫
      SX.map (Prod.mkHom (factor.hom.app OY) (factor.hom.app OY)) =
      factor.hom.app (TY.obj (OY, OY)) ≫ QX.map c ≫ iF.hom)
    (ht : iF.hom ≫ SX.map (Prod.mkHom (QX.map a.hom) (QX.map a.hom)) =
      QX.map (TX.map (Prod.mkHom a.hom a.hom)) ≫ iX.hom)
    (hc : L.map mY ≫ a.hom = c ≫ TX.map (Prod.mkHom a.hom a.hom) ≫ mX) :
    H.map (iY.inv ≫ QY.map mY) ≫ (factor.hom.app OY ≫ QX.map a.hom) =
      μ.hom.app (QY.obj OY, QY.obj OY) ≫
        SX.map (Prod.mkHom (factor.hom.app OY ≫ QX.map a.hom)
          (factor.hom.app OY ≫ QX.map a.hom)) ≫
        (iX.inv ≫ QX.map mX) := by
  apply (cancel_epi (H.map iY.hom)).mp
  have hp : Prod.mkHom (factor.hom.app OY ≫ QX.map a.hom)
      (factor.hom.app OY ≫ QX.map a.hom) =
      Prod.mkHom (factor.hom.app OY) (factor.hom.app OY) ≫
        Prod.mkHom (QX.map a.hom) (QX.map a.hom) := rfl
  rw [hp, SX.map_comp]
  simp only [H.map_comp, Category.assoc]
  rw [← H.map_comp_assoc, Iso.hom_inv_id, H.map_id, Category.id_comp]
  simp only [← Category.assoc] at hμ ⊢
  rw [hμ]
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  simp only [Iso.hom_inv_id_assoc]
  have hn := factor.hom.naturality mY
  change H.map (QY.map mY) ≫ factor.hom.app OY =
    factor.hom.app (TY.obj (OY, OY)) ≫ QX.map (L.map mY) at hn
  rw [reassoc_of% hn, ← QX.map_comp, hc]
  simp only [QX.map_comp]

namespace WeilConjectures.CompletedUnitPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private abbrev J (W : Scheme.{u}) := coefficientSequenceTopology (Scheme.ProEt.topology W)
private abbrev A (W : Scheme.{u}) := coefficientSequenceCommRingSheaf l E W
private abbrev O (W : Scheme.{u}) := ringedTensorUnitComplex.{u+1,u,u} (J W) (A l E W)
private abbrev ringMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((sheafCompose _ (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (A l E Y)) ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous RingCat.{u+1}
        (J Y) (J X)).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (A l E X)) :=
  ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})⟩
private instance ringMapRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u+1} (ringMap l E f)).IsRightAdjoint :=
  pullbackTensorSequenceDirect_rightAdjoint l E f
private instance baseFinal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceBase f).Final := by
  unfold pullbackTensorSequenceBase
  infer_instance
private def unitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceInverse l E f).obj (systemUnit l E Y) ≅ systemUnit l E X :=
  asIso (SheafOfModules.pullbackObjUnitToUnit (ringMap l E f))
private def chainUnitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj (O l E Y) ≅
      O l E X :=
  (HomologicalComplex.singleMapHomologicalComplex
    (pullbackTensorSequenceInverse l E f) (.up ℤ) 0).app (systemUnit l E Y) ≪≫
      (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso (unitPullback l E f)
set_option maxHeartbeats 800000 in
-- Normalize the single-complex comparison before inspecting scalar sections.
private theorem chainUnitPullback_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : ℕ × Y.ProEt) (a : (A l E Y).obj.obj (op V)) :
    (((chainUnitPullback l E f).hom.f 0).val.app
        (op ((pullbackTensorSequenceBase f).obj V)))
      (((pullbackTensorSequenceAdjunction l E f).unit.app ((O l E Y).X 0)).val.app (op V)
        (ringedTensorUnitSection.{u+1,u,u} (J Y) (A l E Y) (op V) a)) =
      ringedTensorUnitSection.{u+1,u,u} (J X) (A l E X)
        (op ((pullbackTensorSequenceBase f).obj V))
        ((pullbackTensorSequenceRing l E f).hom.app (op V) a) := by
  let F := pullbackTensorSequenceInverse l E f
  let G := pullbackTensorSequenceDirect l E f
  let adj := pullbackTensorSequenceAdjunction l E f
  let sB := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) (systemUnit l E Y)
  let sA := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) (systemUnit l E X)
  have he : (chainUnitPullback l E f).hom.f 0 ≫ sA.hom =
      F.map sB.hom ≫ (unitPullback l E f).hom := by
    dsimp only [chainUnitPullback, Iso.trans_hom, Functor.mapIso_hom,
      HomologicalComplex.comp_f, Iso.app_hom, F, O, ringedTensorUnitComplex, sA, sB,
      systemUnit, J, A]
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hj : adj.unit.app (systemUnit l E Y) ≫ G.map (unitPullback l E f).hom =
      SheafOfModules.unitToPushforwardObjUnit (ringMap l E f) := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (ringMap l E f)
  have hn := adj.unit.naturality sB.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  change sB.hom ≫ adj.unit.app (systemUnit l E Y) =
    adj.unit.app ((O l E Y).X 0) ≫ G.map (F.map sB.hom) at hn
  have hη : adj.unit.app ((O l E Y).X 0) ≫
      G.map ((chainUnitPullback l E f).hom.f 0 ≫ sA.hom) =
      sB.hom ≫ SheafOfModules.unitToPushforwardObjUnit (ringMap l E f) := by
    rw [he, G.map_comp, ← Category.assoc, ← hn, Category.assoc, hj]
  let WX := op ((pullbackTensorSequenceBase f).obj V)
  have hv := congrArg (fun g ↦ g.val.app (op V) (sB.inv.val.app (op V) a)) hη
  change sA.hom.val.app WX
      (((chainUnitPullback l E f).hom.f 0).val.app WX
        ((adj.unit.app ((O l E Y).X 0)).val.app (op V) (sB.inv.val.app (op V) a))) =
    (SheafOfModules.unitToPushforwardObjUnit (ringMap l E f)).val.app (op V)
      (sB.hom.val.app (op V) (sB.inv.val.app (op V) a)) at hv
  have hb : sB.hom.val.app (op V) (sB.inv.val.app (op V) a) = a := by
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using
      congrArg (fun g ↦ g.val.app (op V) a) sB.inv_hom_id
  rw [hb, SheafOfModules.unitToPushforwardObjUnit_val_app_apply] at hv
  have hh := congrArg (fun z ↦ sA.inv.val.app WX z) hv
  have ha (z : ((O l E X).X 0).val.obj WX) :
      sA.inv.val.app WX (sA.hom.val.app WX z) = z := by
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using
      congrArg (fun g ↦ g.val.app WX z) sA.hom_inv_id
  rw [ha] at hh
  exact hh

private local instance sequenceMonoidal (W : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E W) :=
  SheafOfModules.monoidalCategory (A l E W)
private local instance sequencePreadditive (W : Scheme.{u}) :
    MonoidalPreadditive (coefficientSequenceModules l E W) :=
  SheafOfModules.cochainModulesPreadditive (A l E W)
private local instance sequenceLeftColim (W : Scheme.{u}) (M : coefficientSequenceModules l E W) :
    PreservesColimitsOfSize.{0,0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (A l E W) M
private local instance sequenceRightColim (W : Scheme.{u}) (M : coefficientSequenceModules l E W) :
    PreservesColimitsOfSize.{0,0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits (A l E W) M
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
attribute [local implicit_reducible] coefficientTotalTensor
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.mapHomologicalComplex
set_option maxHeartbeats 1600000 in
-- Transposition checks arbitrary homogeneous summands of the sheaf total tensor.
private theorem chain_leftUnitor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).map (λ_ P).hom =
      (pullbackTensorSequenceCochain l E f).hom.app (O l E Y, P) ≫
        (coefficientTotalTensor.{u,u+1,u} (J X) (A l E X)).map
          (Prod.mkHom (chainUnitPullback l E f).hom (𝟙 _)) ≫
        (λ_ (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex
          (.up ℤ)).obj P)).hom := by
  let F := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let U := O l E Y
  let : (pullbackTensorSequenceDirect l E f).Additive :=
    (pullbackTensorSequenceAdjunction l E f).right_adjoint_additive
  let adj := (pullbackTensorSequenceAdjunction l E f).mapHomologicalComplex (.up ℤ)
  let κ := pullbackTensorSequenceCochain l E f
  let α := chainUnitPullback l E f
  have hκ := (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
  have hbB := (CategoryTheory.RingedDerivedNative.complexConstraints.{u+1,u,u}
    (J Y) (A l E Y)).leftUnitor
  have hbA := (CategoryTheory.RingedDerivedNative.complexConstraints.{u+1,u,u}
    (J X) (A l E X)).leftUnitor
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality (λ_ P).hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn]
  apply CategoryTheory.RingedForgetTensorTransposition.total_hom_ext.{u+1,u,u}
    (J Y) (A l E Y) U P _
  intro n i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by omega
    subst j
    apply CategoryTheory.RingedForgetTensorTransposition.pure_ext.{u+1,u,u}
      (J Y) (A l E Y) _ _ _
    intro W x y
    let WX := op ((pullbackTensorSequenceBase f).obj W.unop)
    let sy := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) (systemUnit l E Y)
    let a : (A l E Y).obj.obj W := sy.hom.val.app W x
    have hx : ringedTensorUnitSection.{u+1,u,u} (J Y) (A l E Y) W a = x := by
      exact congrArg (fun f ↦ f.val.app W x) sy.hom_inv_id
    have hpure : ((κ.hom.app (U, P)).f n).val.app WX
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          (((coefficientTotalTensor.{u,u+1,u} (J Y) (A l E Y)).obj (U,P)).X n)).val.app W
            (coefficientTensorGenerator.{u,u+1,u} (J Y) (A l E Y)
              U P 0 n n hij W x y)) =
      coefficientTensorGenerator.{u,u+1,u} (J X) (A l E X) (F.obj U) (F.obj P)
        0 n n hij WX
        (((pullbackTensorSequenceAdjunction l E f).unit.app (U.X 0)).val.app W x)
        (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W y) := by
      unfold κ pullbackTensorSequenceCochain pullbackTensorUniqueChoice
      exact hκ U P 0 n n hij W.unop x y
    have hmap := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u+1,u,u}
      α.hom (𝟙 (F.obj P)) 0 n n hij WX
      (((pullbackTensorSequenceAdjunction l E f).unit.app (U.X 0)).val.app W x)
      (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W y)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hmap
    have hunit := chainUnitPullback_sections l E f W.unop a
    rw [hx] at hunit
    change ((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W
        (((λ_ P).hom.f n).val.app W
          (coefficientTensorGenerator.{u,u+1,u} (J Y) (A l E Y) U P 0 n n hij W x y)) =
      ((λ_ (F.obj P)).hom.f n).val.app WX
        ((((coefficientTotalTensor.{u,u+1,u} (J X) (A l E X)).map
            (Prod.mkHom α.hom (𝟙 (F.obj P)))).f n).val.app WX
          (((κ.hom.app (U,P)).f n).val.app WX
            (((pullbackTensorSequenceAdjunction l E f).unit.app
              (((coefficientTotalTensor.{u,u+1,u} (J Y) (A l E Y)).obj (U,P)).X n)).val.app W
                (coefficientTensorGenerator.{u,u+1,u} (J Y) (A l E Y)
                  U P 0 n n hij W x y))))
    let τ := fun z ↦ ((λ_ (F.obj P)).hom.f n).val.app WX
      ((((coefficientTotalTensor.{u,u+1,u} (J X) (A l E X)).map
        (Prod.mkHom α.hom (𝟙 (F.obj P)))).f n).val.app WX z)
    let β := fun z ↦ ((λ_ (F.obj P)).hom.f n).val.app WX z
    have h1 := congrArg τ hpure
    have h2 := congrArg β hmap
    have h3 := congrArg (fun z ↦ β
      (coefficientTensorGenerator.{u,u+1,u} (J X) (A l E X)
        (O l E X) (F.obj P) 0 n n hij WX z
        (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W y))) hunit
    have h4 := hbA (F.obj P) n hij WX
      ((pullbackTensorSequenceRing l E f).hom.app W a)
      (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W y)
    change β (coefficientTensorGenerator.{u,u+1,u} (J X) (A l E X)
      (O l E X) (F.obj P) 0 n n hij WX
      (ringedTensorUnitSection.{u+1,u,u} (J X) (A l E X) WX
        ((pullbackTensorSequenceRing l E f).hom.app W a))
      (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W y)) = _ at h4
    have hb := hbB P n hij W a y
    change ((λ_ P).hom.f n).val.app W
      (coefficientTensorGenerator.{u,u+1,u} (J Y) (A l E Y) U P 0 n n hij W
        (ringedTensorUnitSection.{u+1,u,u} (J Y) (A l E Y) W a) y) = a • y at hb
    rw [hx] at hb
    have hleft := congrArg
      (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W) hb
    exact hleft.trans
      (((((pullbackTensorSequenceAdjunction l E f).unit.app (P.X n)).val.app W).hom.map_smul
        a y).trans (h1.trans (h2.trans (h3.trans h4))).symm)
  · apply IsZero.eq_of_src
    apply (tensorRight (P.X j)).map_isZero
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi

private theorem total_tensor_map (W : Scheme.{u})
    {P P' Q Q' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (coefficientTotalTensor.{u,u+1,u} (J W) (A l E W)).map (Prod.mkHom f g) = f ⊗ₘ g := by
  exact CategoryTheory.RingedForgetTensorTransposition.total_map_generic _ f g

set_option maxHeartbeats 1600000 in
-- Match the total-tensor functor with the complex monoidal tensor.
private theorem chain_multiplication {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).map
        (regularUnitComplex_multiplication l E Y).hom ≫ (chainUnitPullback l E f).hom =
      (pullbackTensorSequenceCochain l E f).hom.app (O l E Y, O l E Y) ≫
        (coefficientTotalTensor.{u,u+1,u} (J X) (A l E X)).map
          (Prod.mkHom (chainUnitPullback l E f).hom (chainUnitPullback l E f).hom) ≫
        (regularUnitComplex_multiplication l E X).hom := by
  change _ ≫ _ = _ ≫ _ ≫ (λ_ (O l E X)).hom
  rw [show (regularUnitComplex_multiplication l E Y).hom = (λ_ (O l E Y)).hom from rfl,
    chain_leftUnitor l E f (O l E Y)]
  simp only [Category.assoc]
  rw [← MonoidalCategory.leftUnitor_naturality]
  rw [total_tensor_map, total_tensor_map]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [Category.comp_id]

set_option maxHeartbeats 800000 in
-- Normalize the exact-derived comparison against its cochain factorization.
private theorem chainUnitPullback_localization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorSystemRegularPullback l E f).hom =
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app (O l E Y) ≫
        DerivedCategory.Q.map (chainUnitPullback l E f).hom := by
  let F := pullbackTensorSequenceInverse l E f
  have h : (F.mapDerivedCategorySingleFunctor 0).hom.app (systemUnit l E Y) =
      F.mapDerivedCategoryFactors.hom.app (O l E Y) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (systemUnit l E Y)) := by
    apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app (O l E Y))).mp
    simp only [Iso.inv_hom_id_app_assoc]
    exact F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (systemUnit l E Y)
  change (F.mapDerivedCategorySingleFunctor 0).hom.app (systemUnit l E Y) ≫
    (DerivedCategory.singleFunctor (coefficientSequenceModules l E X) 0).map
      (unitPullback l E f).hom = _
  rw [h]
  simp only [chainUnitPullback, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

set_option maxHeartbeats 1600000 in
-- Specialize the tensor-model square at the two regular unit complexes.
/-- Ordinary coefficient-ring pullback preserves regular multiplication after localization.
Source: Stacks 07A4 and 0941; purity transport Step 2 on the coefficient unit.
(blueprint: lem-pur-completed-unit-regular-pullback-multiplication).

Proof: work first with the regular unit complex and its degree-zero scalar
multiplication. At ordinary sheaf level, transpose along the specified pullback
adjunction and evaluate on the generating section one: both composites multiply
the two structural images of the scalars. The coefficient map preserves products,
and the adjunction unit inserts one. Sheafification and total tensor preserve the
equality of these maps. Localize and use the exact-derived single comparison and
the defining K-flat square of pullbackTensorSystemComparison. Naturality of the
tensor model cancels the two representative comparisons, giving the stated square.
No closed-unit coordinate isomorphism or integral category occurs in this step. -/
theorem regularSystemPullback_multiplication {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceDerived l E f).map (regularSystemMultiplication l E Y).hom ≫
        (tensorSystemRegularPullback l E f).hom =
      (pullbackTensorSystemComparison l E f).hom.app
        (systemObject l E Y, systemObject l E Y) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom (tensorSystemRegularPullback l E f).hom
            (tensorSystemRegularPullback l E f).hom) ≫
        (regularSystemMultiplication l E X).hom  := by
  let F := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let U := coefficientTotalTensor.{u,u+1,u} (J X) (A l E X)
  let a := chainUnitPullback l E f
  have hY := regularUnitComplex_kFlat l E Y
  have hX := regularUnitComplex_kFlat l E X
  have hF := pullbackTensorSequenceGood l E f (O l E Y) hY
  have hn := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec
    (O l E Y) (O l E Y) hY hY
  change (pullbackTensorSequenceDerived l E f).map
      (pullbackTensorSystemModel l E Y (O l E Y) (O l E Y) hY hY).hom ≫
    (pullbackTensorSystemComparison l E f).hom.app
      (DerivedCategory.Q.obj (O l E Y), DerivedCategory.Q.obj (O l E Y)) ≫
    TX.map (Prod.mkHom
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app (O l E Y))
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app (O l E Y))) = _
    at hn
  have ht : (pullbackTensorSystemModel l E X (F.obj (O l E Y)) (F.obj (O l E Y))
      hF hF).hom ≫
      TX.map (Prod.mkHom (DerivedCategory.Q.map a.hom) (DerivedCategory.Q.map a.hom)) =
    DerivedCategory.Q.map (U.map (Prod.mkHom a.hom a.hom)) ≫
      (pullbackTensorSystemModel l E X (O l E X) (O l E X) hX hX).hom := by
    exact ((pullbackTensorCalculus l E X).systemTensorModel.comparison.hom.naturality
      (Prod.mkHom
        (ObjectProperty.homMk (X := ⟨F.obj (O l E Y), hF⟩)
          (Y := ⟨O l E X, hX⟩) a.hom)
        (ObjectProperty.homMk (X := ⟨F.obj (O l E Y), hF⟩)
          (Y := ⟨O l E X, hX⟩) a.hom))).symm
  have h := multiplication_model_square
    DerivedCategory.Q DerivedCategory.Q F (pullbackTensorSequenceDerived l E f)
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors
    (coefficientTotalTensor.{u,u+1,u} (J Y) (A l E Y)) U
    (pullbackTensorCalculus l E Y).systemClosed.tensor TX
    (pullbackTensorSystemComparison l E f) (O l E Y) (O l E X)
    (pullbackTensorSystemModel l E Y (O l E Y) (O l E Y) hY hY)
    (pullbackTensorSystemModel l E X (F.obj (O l E Y)) (F.obj (O l E Y)) hF hF)
    (pullbackTensorSystemModel l E X (O l E X) (O l E X) hX hX)
    a (regularUnitComplex_multiplication l E Y).hom
    (regularUnitComplex_multiplication l E X).hom
    ((pullbackTensorSequenceCochain l E f).hom.app (O l E Y, O l E Y))
    hn ht (chain_multiplication l E f)
  simpa only [regularSystemMultiplication, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, chainUnitPullback_localization, pullbackTensorSystemModel,
    systemObject, O, ringedTensorUnitComplex, systemUnit, J, A, a, TX,
    DerivedCategory.Q_obj_single_obj, Category.assoc] using h

end WeilConjectures.CompletedUnitPullback
