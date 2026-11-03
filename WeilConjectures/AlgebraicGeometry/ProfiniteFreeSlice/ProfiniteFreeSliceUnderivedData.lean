/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceGeometricData

/-! # The underived profinite free-sheaf Hom calculation

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-f3-profinite-free-slice-underived-data).

The remaining underived obligation is an isomorphism of module sheaf functors,
not only a bijection on individual sections. Its evaluation field prescribes the
map on the projection generator after the fixed section-to-slice comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

-- Avoid the universe-mismatched global instance exposed by newer imports.
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
attribute [local instance 1000001] sectionRingHasSheafCompose sectionModulesGrothendieck
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

private abbrev sectionSets : Modules Λ X ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget Ab.{u + 1})

private def sectionFreeAdjunction : localFree Λ X ⋙ (equivalence Λ X).functor ⊣
    sectionSets Λ X := by
  let E := equivalence Λ X
  exact ((localFreeAdjunction Λ X).comp E.toAdjunction).ofNatIsoRight
    (Functor.isoWhiskerRight E.counitIso (sectionSets Λ X))

private abbrev sectionFree : Modules Λ X :=
  (equivalence Λ X).functor.obj (freeOnTest Λ X P)

private def freeYonedaEquiv (M : Modules Λ X) :
    (sectionFree Λ X P ⟶ M) ≃ M.val.obj (op (test X P)) :=
  ((sectionFreeAdjunction Λ X).homEquiv (represented X P) M).trans
    (Scheme.ProEt.topology X).uliftYonedaEquiv

omit [IsCommMonObj Λ] in
private theorem testGenerator_map {V W : X.ProEt} (f : V ⟶ W)
    (a : W ⟶ test X P) :
    (freeOnTest Λ X P).X.obj.map f.op (testGenerator Λ X P W a) =
      testGenerator Λ X P V (f ≫ a) := by
  have h := congrArg (fun z ↦ z (ULift.up a))
    (((localFreeAdjunction Λ X).unit.app (represented X P)).hom.naturality f.op)
  exact h.symm

set_option maxHeartbeats 1600000 in
-- The composed equivalences involve two presentations of the underlying set sheaf.
private theorem freeYonedaEquiv_apply (M : Modules Λ X) (f : sectionFree Λ X P ⟶ M) :
    freeYonedaEquiv Λ X P M f =
      (f.val.app (op (test X P))).hom
        (testGenerator Λ X P (test X P) (𝟙 _)) := by
  let E := equivalence Λ X
  have h := (E.toAdjunction.homEquiv (freeOnTest Λ X P) M).symm_apply_apply f
  change E.functor.map (E.toAdjunction.homEquiv _ _ f) ≫
    E.counitIso.hom.app M = f at h
  dsimp only [freeYonedaEquiv, Equiv.trans_apply]
  change (((sectionFreeAdjunction Λ X).homEquiv (represented X P) M f).hom.app
      (op (test X P))) (ULift.up (𝟙 (test X P))) = _
  erw [sectionFreeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  erw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit]
  exact congrArg (fun k ↦ (k.val.app (op (test X P))).hom
    (testGenerator Λ X P (test X P) (𝟙 _))) h

set_option maxHeartbeats 1600000 in
-- Infer the slice module structure through both restriction functors.
private def freeOverEquiv (M : Modules Λ X) (V : X.ProEt) :
    (SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P) M).val.obj (op V) ≃
      M.val.obj (op (V ⨯ test X P)) :=
  (SheafOfModules.fullyFaithfulForget _).homEquiv.symm.trans
    (((SheafOfModules.overPushforwardOverAdj V).homEquiv
      (sectionFree Λ X P) (M.over V)).trans
      (freeYonedaEquiv Λ X P _))

private theorem freeOverEquiv_apply (M : Modules Λ X) (V : X.ProEt)
    (φ : (SheafOfModules.homObj (R := ring Λ X)
      (sectionFree Λ X P) M).val.obj (op V)) :
    freeOverEquiv Λ X P M V φ =
      (φ.app (op (Over.mk (prod.fst : V ⨯ test X P ⟶ V)))).hom
        (testGenerator Λ X P (V ⨯ test X P) prod.snd) := by
  erw [freeOverEquiv, Equiv.trans_apply, Equiv.trans_apply, freeYonedaEquiv_apply,
    Adjunction.homEquiv_unit]
  change (φ.app (op ((Over.star V).obj (test X P)))).hom
    ((((SheafOfModules.overPushforwardOverAdj V).unit.app
      (sectionFree Λ X P)).val.app (op (test X P))).hom
        (testGenerator Λ X P (test X P) (𝟙 _))) = _
  erw [SheafOfModules.overPushforwardOverAdj,
    SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app,
    Over.forgetAdjStar_counit_app]
  let a : (Over.star V).obj (test X P) ⟶
      Over.mk (prod.fst : V ⨯ test X P ⟶ V) :=
    Over.homMk (𝟙 _) (by
      change (𝟙 _) ≫ prod.fst = prod.lift prod.fst (𝟙 _) ≫ prod.fst
      simp only [Category.id_comp, prod.lift_fst])
  have h := PresheafOfModules.naturality_apply φ a.op
    (testGenerator Λ X P (V ⨯ test X P) prod.snd)
  change (φ.app (op ((Over.star V).obj (test X P)))).hom
      ((freeOnTest Λ X P).X.obj.map (𝟙 (op (V ⨯ test X P)))
        (testGenerator Λ X P (V ⨯ test X P) prod.snd)) =
    M.val.presheaf.map (𝟙 (op (V ⨯ test X P)))
      ((φ.app (op (Over.mk prod.fst))).hom
        (testGenerator Λ X P (V ⨯ test X P) prod.snd)) at h
  simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at h
  change (φ.app (op ((Over.star V).obj (test X P)))).hom
    ((freeOnTest Λ X P).X.obj.map (prod.snd : V ⨯ test X P ⟶ test X P).op
      (testGenerator Λ X P (test X P) (𝟙 _))) = _
  rw [testGenerator_map, Category.comp_id]
  exact h

private abbrev productToBase (V : X.ProEt) : product X P V ⟶ V :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (test X P).hom (test X P).prop trivial).counit.app V

private def productLift {V W : X.ProEt} (a : W ⟶ V) (b : W ⟶ test X P) :
    W ⟶ product X P V :=
  MorphismProperty.Over.homMk
    (pullback.lift a.left b.left ((MorphismProperty.Over.w a).trans
      (MorphismProperty.Over.w b).symm))
    (by change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        simp only [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w b) trivial

private theorem productLift_fst {V W : X.ProEt} (a : W ⟶ V) (b : W ⟶ test X P) :
    productLift X P a b ≫ productToBase X P V = a := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

private theorem productLift_snd {V W : X.ProEt} (a : W ⟶ V) (b : W ⟶ test X P) :
    productLift X P a b ≫ productToTest X P V = b := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

private theorem product_hom_ext {V W : X.ProEt} (a b : W ⟶ product X P V)
    (hf : a ≫ productToBase X P V = b ≫ productToBase X P V)
    (hs : a ≫ productToTest X P V = b ≫ productToTest X P V) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact congrArg (fun f ↦ f.left) hf
  · exact congrArg (fun f ↦ f.left) hs

private def productIso (V : X.ProEt) : product X P V ≅ V ⨯ test X P where
  hom := prod.lift (productToBase X P V) (productToTest X P V)
  inv := productLift X P prod.fst prod.snd
  hom_inv_id := by
    apply product_hom_ext X P <;>
      simp only [Category.assoc, productLift_fst, productLift_snd,
        prod.lift_fst, prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        productLift_fst, productLift_snd, Category.id_comp]

private theorem lowerScalar (N : Internal Λ (test X P).left) (V : X.ProEt)
    (r : ((ring Λ X).obj.obj (op V)))
    (m : ((equivalence Λ X).functor.obj ((directImage Λ X P).obj N)).val.obj (op V)) :
    r • m =
      ((InternalModuleOperations.coefficientMap Λ (test X P).hom).hom.app (op V)).hom r •
        (show ((equivalence Λ (test X P).left).functor.obj N).val.obj
          (op (baseChanged X P V)) from m) := by
  let c := InternalModuleOperations.lowerComparison Λ (test X P).hom
  have hc := (InternalModuleOperations.lowerComparison_existsUnique Λ
    (test X P).hom).exists.choose_spec
  let F := (c.hom.app N).val.app (op V)
  have h : F.hom (r • m) =
      ((InternalModuleOperations.coefficientMap Λ (test X P).hom).hom.app (op V)).hom r •
        (show ((equivalence Λ (test X P).left).functor.obj N).val.obj
          (op (baseChanged X P V)) from F.hom m) := F.hom.map_smul r m
  calc
    r • m = F.hom (r • m) := (hc N (op V) (r • m)).symm
    _ = _ := h
    _ = _ := congrArg
      (fun n : ((equivalence Λ (test X P).left).functor.obj N).val.obj
          (op (baseChanged X P V)) ↦
        ((InternalModuleOperations.coefficientMap Λ (test X P).hom).hom.app
        (op V)).hom r • n) (hc N (op V) m)

set_option maxHeartbeats 1600000 in
-- Normalize the scalar restriction along the section-module comparison.
private theorem sectionToSlice_smul (M : Internal Λ X) (V : X.ProEt)
    (r : (ring Λ X).obj.obj (op V))
    (m : ((equivalence Λ X).functor.obj M).val.obj (op (product X P V))) :
    (sectionToSlice Λ X P M V).hom
        ((ring Λ X).obj.map (productToBase X P V).op r • m) =
      r • (show (((equivalence Λ X).functor.obj
        ((restriction Λ X P ⋙ directImage Λ X P).obj M)).val.obj (op V)) from
          (sectionToSlice Λ X P M V).hom m) := by
  let N := (restriction Λ X P).obj M
  let A := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (test X P).hom (test X P).prop trivial
  let η := InternalModuleOperations.coefficientMap Λ (test X P).hom
  let β := (equivalence Λ X).functor.map
    ((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.app M)
  change ((equivalence Λ (test X P).left).functor.obj N).val.map
      (A.unit.app (baseChanged X P V)).op
      ((β.val.app (op (product X P V))).hom
        ((ring Λ X).obj.map (productToBase X P V).op r • m)) = _
  rw [LinearMap.map_smul, lowerScalar]
  rw [PresheafOfModules.map_smul]
  rw [lowerScalar Λ X P N V]
  congr 1
  have hn := congrArg (fun k ↦ k r) (η.hom.naturality (productToBase X P V).op)
  change (η.hom.app (op (product X P V))).hom
      ((ring Λ X).obj.map (productToBase X P V).op r) =
    (ring Λ (test X P).left).obj.map
      ((Scheme.proEtaleBaseChange (test X P).hom).map (productToBase X P V)).op
        ((η.hom.app (op V)).hom r) at hn
  change (((ring Λ (test X P).left).obj.map
      (A.unit.app (baseChanged X P V)).op)
        ((η.hom.app (op (product X P V))).hom
          ((ring Λ X).obj.map (productToBase X P V).op r))) = _
  rw [hn]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    A.right_triangle_components]
  erw [op_id, CategoryTheory.Functor.map_id]
  rfl

private def freeEvaluation (M : Modules Λ X) (V : X.ProEt)
    (φ : (SheafOfModules.homObj (R := ring Λ X)
      (sectionFree Λ X P) M).val.obj (op V)) : M.val.obj (op (product X P V)) :=
  (φ.app (op (Over.mk (productToBase X P V)))).hom
    (testGenerator Λ X P (product X P V) (productToTest X P V))

private theorem freeEvaluation_eq (M : Modules Λ X) (V : X.ProEt)
    (φ : (SheafOfModules.homObj (R := ring Λ X)
      (sectionFree Λ X P) M).val.obj (op V)) :
    freeEvaluation Λ X P M V φ =
      M.val.map (productIso X P V).hom.op (freeOverEquiv Λ X P M V φ) := by
  rw [freeOverEquiv_apply]
  let a : Over.mk (productToBase X P V) ⟶
      Over.mk (prod.fst : V ⨯ test X P ⟶ V) :=
    Over.homMk (productIso X P V).hom (by simp [productIso])
  have h := PresheafOfModules.naturality_apply φ a.op
    (testGenerator Λ X P (V ⨯ test X P) prod.snd)
  change (φ.app (op (Over.mk (productToBase X P V)))).hom
      ((freeOnTest Λ X P).X.obj.map (productIso X P V).hom.op
        (testGenerator Λ X P (V ⨯ test X P) prod.snd)) =
    M.val.map (productIso X P V).hom.op
      ((φ.app (op (Over.mk prod.fst))).hom
        (testGenerator Λ X P (V ⨯ test X P) prod.snd)) at h
  rw [testGenerator_map] at h
  have hp : (productIso X P V).hom ≫ prod.snd = productToTest X P V :=
    prod.lift_snd _ _
  erw [hp] at h
  change freeEvaluation Λ X P M V φ = _ at h
  exact h

private theorem freeEvaluation_bijective (M : Modules Λ X) (V : X.ProEt) :
    Function.Bijective (freeEvaluation Λ X P M V) := by
  have h : Function.Bijective (M.val.map (productIso X P V).hom.op) := by
    change Function.Bijective (M.val.presheaf.map (productIso X P V).hom.op)
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have he : freeEvaluation Λ X P M V = fun φ ↦
      M.val.map (productIso X P V).hom.op (freeOverEquiv Λ X P M V φ) :=
    funext (freeEvaluation_eq Λ X P M V)
  rw [he]
  exact h.comp (freeOverEquiv Λ X P M V).bijective

private abbrev productMap {V W : X.ProEt} (f : V ⟶ W) :
    product X P V ⟶ product X P W :=
  (MorphismProperty.Over.map (f := (test X P).hom) ⊤ (test X P).prop).map
    ((Scheme.proEtaleBaseChange (test X P).hom).map f)

private theorem productMap_fst {V W : X.ProEt} (f : V ⟶ W) :
    productMap X P f ≫ productToBase X P W = productToBase X P V ≫ f :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (test X P).hom (test X P).prop trivial).counit.naturality f

private theorem productMap_snd {V W : X.ProEt} (f : V ⟶ W) :
    productMap X P f ≫ productToTest X P W = productToTest X P V := by
  apply MorphismProperty.Over.Hom.ext
  exact MorphismProperty.Over.w ((Scheme.proEtaleBaseChange (test X P).hom).map f)

private theorem freeEvaluation_naturality (M : Modules Λ X) {V W : X.ProEt}
    (f : V ⟶ W) (φ : (SheafOfModules.homObj (R := ring Λ X)
      (sectionFree Λ X P) M).val.obj (op W)) :
    freeEvaluation Λ X P M V
        ((SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P) M).val.map f.op φ) =
      M.val.map (productMap X P f).op (freeEvaluation Λ X P M W φ) := by
  let a : Over.mk (productToBase X P V ≫ f) ⟶ Over.mk (productToBase X P W) :=
    Over.homMk (productMap X P f) (productMap_fst X P f)
  have h := PresheafOfModules.naturality_apply φ a.op
    (testGenerator Λ X P (product X P W) (productToTest X P W))
  change (φ.app (op (Over.mk (productToBase X P V ≫ f)))).hom _ = _
  change (φ.app (op (Over.mk (productToBase X P V ≫ f)))).hom
      ((freeOnTest Λ X P).X.obj.map (productMap X P f).op
        (testGenerator Λ X P (product X P W) (productToTest X P W))) =
    M.val.map (productMap X P f).op (freeEvaluation Λ X P M W φ) at h
  rw [testGenerator_map, productMap_snd] at h
  exact h

private theorem sectionToSlice_naturality (M : Internal Λ X) {V W : X.ProEt}
    (f : V ⟶ W) (m : M.X.obj.obj (op (product X P W))) :
    (sectionToSlice Λ X P M V).hom (M.X.obj.map (productMap X P f).op m) =
      (((restriction Λ X P ⋙ directImage Λ X P).obj M).X.obj.map f.op)
        ((sectionToSlice Λ X P M W).hom m) := by
  let A := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (test X P).hom (test X P).prop trivial
  let N := (restriction Λ X P).obj M
  let β := ((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.app M).hom.hom
  have h := congrArg (fun k ↦ k.hom m) (β.naturality (productMap X P f).op)
  change (β.app (op (product X P V))).hom
      (M.X.obj.map (productMap X P f).op m) =
    N.X.obj.map ((Scheme.proEtaleBaseChange (test X P).hom).map
      (productMap X P f)).op
      ((β.app (op (product X P W))).hom m) at h
  change N.X.obj.map (A.unit.app (baseChanged X P V)).op
      ((β.app (op (product X P V))).hom (M.X.obj.map (productMap X P f).op m)) = _
  rw [h]
  change N.X.obj.map (A.unit.app (baseChanged X P V)).op
      (N.X.obj.map ((Scheme.proEtaleBaseChange (test X P).hom).map
        (productMap X P f)).op _) =
    N.X.obj.map ((Scheme.proEtaleBaseChange (test X P).hom).map f).op
      (N.X.obj.map (A.unit.app (baseChanged X P W)).op _)
  let n := (β.app (op (product X P W))).hom m
  change N.X.obj.map (A.unit.app (baseChanged X P V)).op
      (N.X.obj.map ((Scheme.proEtaleBaseChange (test X P).hom).map
        (productMap X P f)).op n) =
    N.X.obj.map ((Scheme.proEtaleBaseChange (test X P).hom).map f).op
      (N.X.obj.map (A.unit.app (baseChanged X P W)).op n)
  have ht := congrArg (fun k ↦ N.X.obj.map k.op)
    (A.unit.naturality ((Scheme.proEtaleBaseChange (test X P).hom).map f))
  have hv := ConcreteCategory.congr_hom ht n
  simp only [op_comp, Functor.map_comp, Functor.comp_map, Functor.id_map,
    Functor.id_obj, ConcreteCategory.comp_apply] at hv
  exact hv.symm

private def freeSliceApp (M : Internal Λ X) (V : X.ProEt) :
    (SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P)
      ((equivalence Λ X).functor.obj M)).val.obj (op V) ⟶
    (((equivalence Λ X).functor.obj
      ((restriction Λ X P ⋙ directImage Λ X P).obj M)).val.obj (op V)) :=
  ModuleCat.ofHom
    (X := (SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P)
      ((equivalence Λ X).functor.obj M)).val.obj (op V))
    (Y := ((equivalence Λ X).functor.obj
      ((restriction Λ X P ⋙ directImage Λ X P).obj M)).val.obj (op V))
    { toFun := fun φ ↦ (sectionToSlice Λ X P M V).hom
        (freeEvaluation Λ X P ((equivalence Λ X).functor.obj M) V φ)
      map_add' := fun φ ψ ↦ by
        change (sectionToSlice Λ X P M V).hom (_ + _) = _
        exact map_add _ _ _
      map_smul' := fun r φ ↦ by
        exact sectionToSlice_smul Λ X P M V r _ }

private theorem freeSliceApp_naturality (M : Internal Λ X) {V W : X.ProEt}
    (f : V ⟶ W) :
    (SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P)
        ((equivalence Λ X).functor.obj M)).val.map f.op ≫
      (ModuleCat.restrictScalars ((ring Λ X).obj.map f.op).hom).map
        (freeSliceApp Λ X P M V) =
    freeSliceApp Λ X P M W ≫
      (((equivalence Λ X).functor.obj
        ((restriction Λ X P ⋙ directImage Λ X P).obj M)).val.map f.op) := by
  ext φ
  change (sectionToSlice Λ X P M V).hom
      (freeEvaluation Λ X P _ V
        ((SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P)
          ((equivalence Λ X).functor.obj M)).val.map f.op φ)) = _
  rw [freeEvaluation_naturality]
  exact sectionToSlice_naturality Λ X P M f _

private def freeSliceIso (M : Internal Λ X) :
    SheafOfModules.homObj (R := ring Λ X) (sectionFree Λ X P)
      ((equivalence Λ X).functor.obj M) ≅
    (equivalence Λ X).functor.obj ((restriction Λ X P ⋙ directImage Λ X P).obj M) := by
  have h (V : X.ProEt) : IsIso (freeSliceApp Λ X P M V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have := sectionToSlice_isIso Λ X P M V
    exact ((ConcreteCategory.isIso_iff_bijective _).mp
      (show IsIso (sectionToSlice Λ X P M V) from inferInstance)).comp
        (freeEvaluation_bijective Λ X P ((equivalence Λ X).functor.obj M) V)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ asIso (freeSliceApp Λ X P M V.unop))
      (fun {_ _} f ↦ freeSliceApp_naturality Λ X P M f.unop))

private theorem sectionToSlice_moduleNaturality {M N : Internal Λ X} (g : M ⟶ N)
    (V : X.ProEt) (m : M.X.obj.obj (op (product X P V))) :
    (sectionToSlice Λ X P N V).hom ((g.hom.hom.app (op (product X P V))).hom m) =
      ((((restriction Λ X P ⋙ directImage Λ X P).map g).hom.hom.app (op V)).hom
        ((sectionToSlice Λ X P M V).hom m)) := by
  let A := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (test X P).hom (test X P).prop trivial
  have h := congrArg (fun k ↦ (k.hom.hom.app (op (product X P V))).hom m)
    ((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.naturality g)
  change (((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.app
      N).hom.hom.app (op (product X P V))).hom
        ((g.hom.hom.app (op (product X P V))).hom m) =
    (((restriction Λ X P ⋙ directImage Λ X P).map g).hom.hom.app
      (op (product X P V))).hom
        ((((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.app
          M).hom.hom.app (op (product X P V))).hom m) at h
  change (((restriction Λ X P).obj N).X.obj.map
    (A.unit.app (baseChanged X P V)).op) _ = _
  erw [h]
  exact (ConcreteCategory.congr_hom
    (((restriction Λ X P).map g).hom.hom.naturality
      (A.unit.app (baseChanged X P V)).op) _).symm

private def freeSliceNatIso :
    (equivalence Λ X).functor ⋙
      (SheafOfModules.homFunctor (ring Λ X)).obj (op (sectionFree Λ X P)) ≅
    (restriction Λ X P ⋙ directImage Λ X P) ⋙ (equivalence Λ X).functor :=
  NatIso.ofComponents (freeSliceIso Λ X P) (by
    intro M N g
    ext V φ
    change (sectionToSlice Λ X P N V.unop).hom
      (((equivalence Λ X).functor.map g).val.app
        (op (product X P V.unop))
          (freeEvaluation Λ X P ((equivalence Λ X).functor.obj M) V.unop φ)) = _
    exact sectionToSlice_moduleNaturality Λ X P g V.unop _)

/-- The module-level evaluation isomorphism, with its naturality and generator formula.
Source: Stacks Project Tag 08J7 (blueprint: new-f3-profinite-free-slice-underived-data). -/
structure UnderivedComparisonData (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P) where
  iso : (equivalence Λ X).functor ⋙
      (SheafOfModules.homFunctor (ring Λ X)).obj (op ((sectionFreeComplex Λ X P).X 0)) ≅
    (restriction Λ X P ⋙ directImage Λ X P) ⋙ (equivalence Λ X).functor
  evaluation : ∀ (M : Internal Λ X) (V : X.ProEt)
      (φ : (SheafOfModules.homObj (R := ring Λ X) ((sectionFreeComplex Λ X P).X 0)
        ((equivalence Λ X).functor.obj M)).val.obj (op V)),
    ((iso.hom.app M).val.app (op V)) φ =
      (sectionToSlice Λ X P M V).hom
        (((φ.app (op (Over.mk ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
          (test X P).hom (test X P).prop trivial).counit.app V)))).hom)
            (freeSectionGenerator Λ X P freeIso (product X P V) (productToTest X P V)))

/-- The underived free-sheaf Hom calculation, natural in the module.
Source: Stacks Project Tag 08J7; HRS Section 3
(blueprint: new-f3-profinite-free-slice-underived-data).

Proof: restrict the free module on h_U to the slice over V. Composing its
free adjunction with inverse image shows that it remains free on the
restricted set sheaf. That sheaf is represented by V×_X U. Compose the free
adjunction with Yoneda to evaluate at its projection generator. The inverse
sends a section m to the linear map taking the generator indexed by a:W→U
to restriction of m along (W→V,a); extend this prescription linearly and
sheafify. The adjunction identities show that these maps are inverse.
They respect scalars and restrictions, so they define an isomorphism of
module sheaves. They also commute with every map M→M', giving a natural
isomorphism. Transport through freeIso and the degree-zero single-complex
identification, and then use the canonical sectionToSlice map. This gives
exactly the displayed generator evaluation. Empty U and zero coefficients
satisfy the same universal properties. -/
theorem exists_underived_comparison_data
    (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P) :
    Nonempty (UnderivedComparisonData Λ X P freeIso) := by
  let e : (sectionFreeComplex Λ X P).X 0 ≅ sectionFree Λ X P :=
    (equivalence Λ X).functor.mapIso
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (pulledFree Λ X P) ≪≫ freeIso)
  let c := Functor.isoWhiskerLeft (equivalence Λ X).functor
    ((SheafOfModules.homFunctor (ring Λ X)).mapIso e.symm.op)
  refine ⟨⟨c ≪≫ freeSliceNatIso Λ X P, ?_⟩⟩
  intro M V φ
  change (sectionToSlice Λ X P M V).hom
    ((φ.app (op (Over.mk (productToBase X P V)))).hom
      (((e.inv).val.app (op (product X P V))).hom
        (testGenerator Λ X P (product X P V) (productToTest X P V)))) = _
  rfl

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
