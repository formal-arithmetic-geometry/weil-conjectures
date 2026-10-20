/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology

import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.Algebra.Homology.FlatScalarExtensionHomologyAdjunct

/-! # Realization of prescribed tensor cohomology on a K-flat resolution

Source: Stacks Project, Tags 06Y6, 064L, 065Z and 00HD.
(blueprint: lem-pc-prescribed-tensor-cohomology-model-realization). -/

@[expose] public section

set_option autoImplicit false

universe u w v z

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RingTensorCohomology

private theorem extend_quasiIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ L) (ha : QuasiIso a)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K)
    (hL : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat L) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map a) := by
  have : (ModuleCat.extendScalars f).PreservesKFlatQuasiIso :=
    ModuleCat.extendScalars_preservesKFlatQuasiIso f
  exact (ModuleCat.extendScalars f).quasiIso_mapHomologicalComplex_map_of_kFlat hK hL a

private theorem res_kFlat (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      ((resolution R).obj K) :=
  (flatResolution R).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K

private theorem aug_quasiIso (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso ((augmentation R).app K) := by
  dsimp [augmentation]
  infer_instance

private theorem res_quasiIso (R : Type u) [CommRing R]
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K') [QuasiIso f] :
    QuasiIso ((resolution R).map f) := by
  have := aug_quasiIso R K
  have := aug_quasiIso R K'
  rw [← quasiIso_iff_comp_right _ ((augmentation R).app K')]
  rw [(augmentation R).naturality f]
  change QuasiIso ((augmentation R).app K ≫ f)
  infer_instance

private theorem source_isIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ K') [QuasiIso f] :
    IsIso ((source R A B i).map f) := by
  have : QuasiIso ((restrict R A).map f) := inferInstance
  have := res_quasiIso R ((restrict R A).map f)
  have : QuasiIso ((extend R B).map ((resolution R).map ((restrict R A).map f))) :=
    extend_quasiIso _ _ inferInstance
      (res_kFlat R _) (res_kFlat R _)
  change IsIso (HomologicalComplex.homologyMap
    ((extend R B).map ((resolution R).map ((restrict R A).map f))) i)
  infer_instance

private theorem counit_isIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
  let F := ModuleCat.extendScalars (algebraMap R B)
  have : F.PreservesKFlatQuasiIso :=
    ModuleCat.extendScalars_preservesKFlatQuasiIso _
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence
      (ModuleCat.{u} R) (AsSmall.equiv (C := ℤ)).symm
  exact (F.isLeftDerivedFunctor_iff_isIso_app_of_kFlat ε).1 hLF K hK

private noncomputable def counitH
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh) (i : ℤ) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ LF ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) ⟶
    extend R B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i :=
  Functor.whiskerRight
      (Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) ε)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) ≫
    (isoWhiskerLeft
        (HomotopyCategory.quotient _ (.up ℤ) ⋙
          (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i) ≪≫
      isoWhiskerRight
        ((ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategoryFactors (.up ℤ)).symm
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i) ≪≫
      isoWhiskerLeft (extend R B)
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i)).hom

private theorem counitH_isIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (i : ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K) :
    IsIso ((counitH R B LF ε i).app K) := by
  have := counit_isIso R B LF ε hLF K hK
  dsimp [counitH]
  infer_instance

private noncomputable def sourceIso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (i : ℤ) :
    (resolution R ⋙ extend R B ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ LF ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let G := q ⋙ DerivedCategory.Qh ⋙ LF ⋙ H
  let α := Functor.whiskerRight (augmentation R) G
  have : IsIso α := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro K
    have := aug_quasiIso R K
    have : IsIso (DerivedCategory.Qh.map (q.map ((augmentation R).app K))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    change IsIso (H.map (LF.map (DerivedCategory.Qh.map (q.map _))))
    infer_instance
  let β := Functor.whiskerLeft (resolution R) (counitH R B LF ε i)
  have : IsIso β := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro K
    have := counit_isIso R B LF ε hLF ((resolution R).obj K) (res_kFlat R K)
    dsimp [β, counitH]
    infer_instance
  exact (asIso β).symm ≪≫ asIso α

@[reassoc]
private theorem sourceIso_fac
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (i : ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (sourceIso R B LF ε hLF i).hom.app K ≫ (counitH R B LF ε i).app K =
      HomologicalComplex.homologyMap ((extend R B).map ((augmentation R).app K)) i := by
  have (K' : CochainComplex (ModuleCat.{u} R) ℤ) :
      IsIso ((counitH R B LF ε i).app ((resolution R).obj K')) :=
    counitH_isIso R B LF ε hLF i _ (res_kFlat R K')
  have : IsIso (Functor.whiskerLeft (resolution R) (counitH R B LF ε i)) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun K' ↦
      counitH_isIso R B LF ε hLF i _ (res_kFlat R K')
  let G := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
    DerivedCategory.Qh ⋙ LF ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have hn := (counitH R B LF ε i).naturality ((augmentation R).app K)
  change G.map ((augmentation R).app K) ≫ (counitH R B LF ε i).app K =
    (counitH R B LF ε i).app ((resolution R).obj K) ≫
      HomologicalComplex.homologyMap ((extend R B).map ((augmentation R).app K)) i at hn
  dsimp only [sourceIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [Category.assoc, hn]
  simpa only [NatIso.isIso_inv_app, Functor.whiskerLeft_app] using
    IsIso.inv_hom_id_assoc ((counitH R B LF ε i).app ((resolution R).obj K))
      (HomologicalComplex.homologyMap ((extend R B).map ((augmentation R).app K)) i)

private noncomputable def ordinaryIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    restrict R A ⋙ extend R B ≅
      (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
            ).mapHomologicalComplex (.up ℤ) := by
  classical
  choose e he using fun Q : CochainComplex (ModuleCat.{u} A) ℤ ↦
    ModuleCat.exists_baseTensorOrdinaryIso R A B Q
  refine NatIso.ofComponents e ?_
  intro P Q f
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (e Q).hom.f j ((1 : B) ⊗ₜ[R,algebraMap R B] (f.f j x)) =
    ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).map (f.f j))
      ((e P).hom.f j ((1 : B) ⊗ₜ[R,algebraMap R B] x))
  rw [he, he]
  rfl

private noncomputable def ordinaryH
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (restrict R A ⋙ extend R B ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i) ≅
    ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) i ⋙
        ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) := by
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let U := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  refine isoWhiskerRight (ordinaryIso R A B)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i) ≪≫
    NatIso.ofComponents (fun Q ↦ ((F.obj Q).sc i).mapHomologyIso U) ?_
  intro P Q f
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (F.map f)) U

set_option linter.unusedSectionVars false in
private theorem tensorLinearLift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (M N : ModuleCat.{u} (A ⊗[R] B))
    (f : (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ⟶
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = f := by
  refine ⟨ModuleCat.ofHom { toFun := f, map_add' := f.hom.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.induction_on with
    | zero => simpa only [RingHom.id_apply, zero_smul] using f.hom.map_zero
    | tmul a b =>
      have hb (y : M) :
          f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • y) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f y :=
        f.hom.map_smul b y
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.hom.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl


private noncomputable def targetH
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    target R A B i ⟶
      (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) i ⋙
          ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom :=
  Functor.whiskerLeft (resolution A) (ordinaryH R A B i).hom ≫
    Functor.whiskerRight (augmentation A)
      ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) i ⋙
          ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)

private theorem targetH_isIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q) :
    IsIso ((targetH R A B i).app Q) := by
  have := aug_quasiIso A Q
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
  have : QuasiIso (F.map ((augmentation A).app Q)) :=
    extend_quasiIso _ _ inferInstance (res_kFlat A Q) hQ
  have : IsIso (HomologicalComplex.homologyMap (F.map ((augmentation A).app Q)) i) :=
    inferInstance
  change IsIso ((ordinaryH R A B i).hom.app ((resolution A).obj Q) ≫
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        (HomologicalComplex.homologyMap (F.map ((augmentation A).app Q)) i))
  infer_instance

private theorem target_isIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    {Q Q' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Q ⟶ Q') [QuasiIso f] :
    IsIso ((target R A B i).map f) := by
  have := res_quasiIso A f
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
  let U := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have : QuasiIso (F.map ((resolution A).map f)) :=
    extend_quasiIso _ _ inferInstance
      (res_kFlat A Q) (res_kFlat A Q')
  have : IsIso (U.map (HomologicalComplex.homologyMap (F.map ((resolution A).map f)) i)) :=
    inferInstance
  let e := isoWhiskerLeft (resolution A) (ordinaryH R A B i)
  have hn := e.hom.naturality f
  change (target R A B i).map f ≫ e.hom.app Q' =
    e.hom.app Q ≫ U.map (HomologicalComplex.homologyMap (F.map ((resolution A).map f)) i)
    at hn
  have heq : (target R A B i).map f =
      e.hom.app Q ≫ U.map (HomologicalComplex.homologyMap
        (F.map ((resolution A).map f)) i) ≫ e.inv.app Q' := by
    exact (NatIso.naturality_2 e f).symm
  rw [heq]
  infer_instance

private theorem comparison_targetH
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    (comparison R A B i).app Q ≫ (targetH R A B i).app Q =
      HomologicalComplex.homologyMap
        ((extend R B).map ((augmentation R).app ((restrict R A).obj Q))) i ≫
          (ordinaryH R A B i).hom.app Q := by
  have := spanLeft_isIso R A B i
  apply (cancel_epi ((Functor.whiskerRight (spanLeft R A B)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i)).app Q)).1
  dsimp only [comparison, NatTrans.comp_app]
  simp only [NatIso.isIso_inv_app, Category.assoc, IsIso.hom_inv_id_assoc]
  dsimp only [targetH, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  have hn := (ordinaryH R A B i).hom.naturality ((augmentation A).app Q)
  erw [← hn]
  change HomologicalComplex.homologyMap
      ((extend R B).map ((augmentation R).app ((restrict R A).obj ((resolution A).obj Q)))) i ≫
      HomologicalComplex.homologyMap
        ((extend R B).map ((restrict R A).map ((augmentation A).app Q))) i ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp_assoc, ← Functor.map_comp]
  have hnR := (augmentation R).naturality ((restrict R A).map ((augmentation A).app Q))
  dsimp only [Functor.id_map] at hnR
  rw [← hnR]
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

private theorem tensorIsoLift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (M N : ModuleCat.{u} (A ⊗[R] B))
    (e : (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      e.hom ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • e.hom x) :
    ∃ f : M ≅ N,
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map f.hom = e.hom := by
  let U := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  obtain ⟨f, hf⟩ := tensorLinearLift R A B M N e.hom h
  have : IsIso (U.map f) := by rw [hf]; infer_instance
  have : IsIso f := isIso_of_reflects_iso f U
  exact ⟨asIso f, hf⟩

private theorem model_comparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D) (i : ℤ) :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map (L.comparison i) =
    (L.cohomologyIso i).hom ≫
      (counitH R B L.derived L.counit i).app ((restrict R A).obj Q) ≫
        (ordinaryH R A B i).hom.app Q := by
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
  let U := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have ho : L.ordinaryIso.hom = (ordinaryIso R A B).hom.app Q := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (L.ordinaryIso_tmul j 1 x).trans
      (Classical.choose_spec (ModuleCat.exists_baseTensorOrdinaryIso R A B Q) j 1 x).symm
  apply (cancel_mono (((F.obj Q).sc i).mapHomologyIso U).inv).1
  rw [L.comparison_eq i, ho]
  dsimp only [ordinaryH, counitH, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app]
  dsimp only [F, U]
  simp only [Category.assoc, Iso.symm_hom, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, Iso.hom_inv_id, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem sourceIso_beta
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (i : ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (counitH R B LF ε i).app ((resolution R).obj K) ≫
        (sourceIso R B LF ε hLF i).hom.app K =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        (LF.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (.up ℤ)).map ((augmentation R).app K)))) := by
  have (K' : CochainComplex (ModuleCat.{u} R) ℤ) :
      IsIso ((counitH R B LF ε i).app ((resolution R).obj K')) :=
    counitH_isIso R B LF ε hLF i _ (res_kFlat R K')
  have : IsIso (Functor.whiskerLeft (resolution R) (counitH R B LF ε i)) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun K' ↦
      counitH_isIso R B LF ε hLF i _ (res_kFlat R K')
  dsimp only [sourceIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [NatIso.isIso_inv_app, Functor.whiskerLeft_app, IsIso.hom_inv_id_assoc]
  rfl

private theorem counitH_delta
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF LG : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (ε' : DerivedCategory.Qh ⋙ LG ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (δ : LF ⟶ LG) (hδ : Functor.whiskerLeft DerivedCategory.Qh δ ≫ ε' = ε)
    (i : ℤ) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        (δ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) ≫
      (counitH R B LG ε' i).app K = (counitH R B LF ε i).app K := by
  have hd := congrArg (fun t ↦ t.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) hδ
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hd
  dsimp only [counitH, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [← Category.assoc, ← Functor.map_comp, hd]

private theorem sourceIso_delta
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (LF LG : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (ε' : DerivedCategory.Qh ⋙ LG ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (hLG : LG.IsLeftDerivedFunctor ε'
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (δ : LF ⟶ LG) (hδ : Functor.whiskerLeft DerivedCategory.Qh δ ≫ ε' = ε)
    (i : ℤ) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (sourceIso R B LF ε hLF i).hom.app K ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        (δ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) =
      (sourceIso R B LG ε' hLG i).hom.app K := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have := counitH_isIso R B LF ε hLF i _ (res_kFlat R K)
  apply (cancel_epi ((counitH R B LF ε i).app ((resolution R).obj K))).1
  rw [← Category.assoc, sourceIso_beta]
  have hd := congrArg H.map (δ.naturality
    (DerivedCategory.Qh.map (q.map ((augmentation R).app K))))
  simp only [Functor.map_comp] at hd
  dsimp only [H, q, Functor.id_obj] at hd
  rw [hd]
  rw [← sourceIso_beta R B LG ε' hLG i K, ← Category.assoc]
  rw [counitH_delta R B LF LG ε ε' δ hδ i ((resolution R).obj K)]

@[reassoc]
private theorem scalar_inv_naturality
    {V : Type v} [Category.{z} V]
    (A : Type u) [CommRing A] (F : CochainComplex (ModuleCat.{u} A) ℤ ⥤ V)
    {Q U : CochainComplex (ModuleCat.{u} A) ℤ} (f : Q ⟶ U) [IsIso (F.map f)] (a : A) :
    F.map (a • 𝟙 U) ≫ inv (F.map f) = inv (F.map f) ≫ F.map (a • 𝟙 Q) := by
  apply (cancel_epi (F.map f)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← F.map_comp]
  have he : f ≫ (a • 𝟙 U) = (a • 𝟙 Q) ≫ f := by simp
  rw [he, F.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem extension_scalar
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    ((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).map
      (a • 𝟙 Q) = algebraMap A C a •
        𝟙 (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).obj Q) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.ExtendScalars.hom_ext
  intro q
  change ((1 : C) ⊗ₜ[A,algebraMap A C] (a • q)) =
    algebraMap A C a • ((1 : C) ⊗ₜ[A,algebraMap A C] q)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  let V := (ModuleCat.restrictScalars (algebraMap A C)).obj (ModuleCat.of _ C)
  have hv : a • (show V from (1 : C)) = (show V from algebraMap A C a) := by
    change algebraMap A C a * 1 = algebraMap A C a
    rw [mul_one]
  simpa only [hv] using
    (TensorProduct.smul_tmul (R := A) a (show V from (1 : C)) q).symm

private theorem extensionH_scalar
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (i : ℤ) :
    HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).map
        (a • 𝟙 Q)) i = algebraMap A C a •
      𝟙 ((((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).obj Q
        ).homology i) := by
  rw [extension_scalar]
  change ShortComplex.homologyMap (algebraMap A C a •
    𝟙 ((((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).obj Q
      ).sc i)) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

@[reassoc]
private theorem inverse_naturality
    {C : Type v} {D : Type u} [Category.{z} C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    [IsIso (F.map f)] [IsIso (G.map f)] :
    α.app Y ≫ inv (G.map f) = inv (F.map f) ≫ α.app X := by
  apply (cancel_epi (F.map f)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [α.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private noncomputable def localHom
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q))
    (i : ℤ) :
    (ModuleCat.extendScalars g).obj
      ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q).homology i) ⟶
      (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q).homology i :=
  ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm
    (HomologicalComplex.homologyMap φ i ≫
      (((((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q).sc i
        ).mapHomologyIso (ModuleCat.restrictScalars g)).hom)

private theorem localHom_naturality
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D)
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (h : Q ⟶ Q')
    (φ : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q))
    (φ' : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q' ⟶
      ((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q'))
    (hφ : ∀ (j : ℤ) (e : C) (q : Q.X j),
      φ.f j (e ⊗ₜ[A,f] q) = g e ⊗ₜ[A,g.comp f] q)
    (hφ' : ∀ (j : ℤ) (e : C) (q : Q'.X j),
      φ'.f j (e ⊗ₜ[A,f] q) = g e ⊗ₜ[A,g.comp f] q) (i : ℤ) :
    (ModuleCat.extendScalars g).map
        (HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h) i) ≫
      localHom f g Q' φ' i = localHom f g Q φ i ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).map h) i := by
  let F := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  let T := (ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)
  let G := ModuleCat.restrictScalars g
  have hn : F.map h ≫ φ' = φ ≫ (G.mapHomologicalComplex (.up ℤ)).map (T.map h) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.ExtendScalars.hom_ext
    intro q
    change φ'.f j ((1 : C) ⊗ₜ[A,f] (h.f j q)) =
      (ModuleCat.extendScalars (g.comp f)).map (h.f j)
        (φ.f j ((1 : C) ⊗ₜ[A,f] q))
    rw [hφ, hφ']
    rfl
  let adj := ModuleCat.extendRestrictScalarsAdj g
  apply (adj.homEquiv _ _).injective
  dsimp only [localHom]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hm := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (T.map h)) G
  change HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map (T.map h)) i ≫
      (((T.obj Q').sc i).mapHomologyIso G).hom =
    (((T.obj Q).sc i).mapHomologyIso G).hom ≫
      G.map (HomologicalComplex.homologyMap (T.map h) i) at hm
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp_assoc, hn,
    HomologicalComplex.homologyMap_comp, Category.assoc, hm]

set_option maxHeartbeats 800000 in
-- Naturality of the nested cohomology functors requires more than the default elaboration budget.
/-- Realize prescribed lifts and their comparison on any functorial K-flat replacement.
Source: Stacks Project, Tags 06Y6 and 064L (K-flat replacements), 065Z
(the canonical comparison), and 00HD (exact flat extension).
(blueprint: lem-pc-prescribed-tensor-cohomology-model-realization)

Proof: put V=resolution_R(restrict_R(Q)). Its augmentation is a quasi-isomorphism,
and V is R-K-flat. For each supplied L(M), the universal counit is invertible on
V(M); derived extension of the augmentation consequently identifies L(M)'s derived
cohomology of Q(M) with the ordinary extension of V(M). Applying resolution_R to
restrict_R(pi) gives a quasi-isomorphism between R-K-flat complexes, which remains
so after extension to B by the K-flat scalar-extension theorem
[lem-pc-extension-kflat-quasi-iso]. Thus this cohomology is naturally
source(U). Conjugate by
eS and L.cohomologyIso to obtain sigma. Naturality for multiplication by a and hS
show that sigma commutes with a tensor 1. It is B-linear already, so tensor
induction upgrades it to a tensor-algebra-linear isomorphism.
For the target use the common span resolution_A(Q) to Q and resolution_A(U),
whose arrows are augmentation_A(Q) and resolution_A(pi). Both are
quasi-isomorphisms between A-K-flat complexes and remain so after extension to
A tensor_R B by [lem-pc-extension-kflat-quasi-iso]. Ordinary tensor associativity and eT
identify target(U) with
cohomology of the latter complex. The equation hT upgrades this identification
to tensor-algebra-linearity. The span identifies it with ordinary tensor cohomology
of Q. Flat extension to D commutes with cohomology; its canonical homology adjunct
and tensor associativity give gamma. Every map in these spans is natural, giving
gamma's naturality. For each g, use the unique counit-compatible isomorphism
between L(M).derived and L(N).derived. Under sigma, S.map g is cohomology of
L(M).derived applied to Q.map g followed by that isomorphism, giving the stated
model-map equation. Finally hc identifies c with the comparison computed on the
common R-K-flat span, and comparison_eq identifies L.comparison with its counit.
Extend this comparison to D and compose with the same canonical homology adjunct
used in gamma. Scalar-extension adjunction and localized_eq identify the result
with L.localizedComparison, proving the final equation. No localization or comparison
between different base rings
is asserted here. The zero replacement and identity replacement satisfy the same
construction, and no boundedness or flatness of B over R is used. -/
theorem prescribedTensorCohomology_model_realization
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [Algebra A D] [IsScalarTower A (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (E : Type v) [Category.{z} E]
    (U Q : E ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (pi : Q ⟶ U) (hpi : ∀ M, QuasiIso (pi.app M))
    (hQ : ∀ M, (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat (Q.obj M))
    (i : ℤ)
    (S T : E ⥤ ModuleCat.{u} (A ⊗[R] B))
    (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
      U ⋙ source R A B i)
    (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
      U ⋙ target R A B i)
    (c : S ⟶ T)
    (hS : ∀ (M : E) (a : A) (x : S.obj M),
      eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (source R A B i).map (a • 𝟙 (U.obj M)) (eS.hom.app M x))
    (hT : ∀ (M : E) (a : A) (x : T.obj M),
      eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (target R A B i).map (a • 𝟙 (U.obj M)) (eT.hom.app M x))
    (hc : Functor.whiskerRight c
        (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
      eS.hom ≫ Functor.whiskerLeft U (comparison R A B i))
    (hf : (algebraMap (A ⊗[R] B) D).Flat)
    (L : ∀ M : E, ModuleCat.BaseDerivedTensorCohomologyModel R A B (Q.obj M) D) :
    ∃ (sigma : ∀ M : E, S.obj M ≅ (L M).cohomology i)
      (gamma : ∀ M : E,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (T.obj M) ≅
          (((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
            (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj
              (Q.obj M)).homology i),
      (∀ (M N : E) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (T.map g) ≫
            (gamma N).hom =
          (gamma M).hom ≫ HomologicalComplex.homologyMap
            (((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).map (Q.map g)) i) ∧
      (∀ (M N : E) (g : M ⟶ N),
        ∃ delta : (L M).derived ⟶ (L N).derived,
          Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) delta ≫
              (L N).counit = (L M).counit ∧
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
              ((sigma M).inv ≫ S.map g ≫ (sigma N).hom) ≫ ((L N).cohomologyIso i).hom =
            ((L M).cohomologyIso i).hom ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
                ((L M).derived.map (DerivedCategory.Qh.map
                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                    ((restrict R A).map (Q.map g))))) ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
                (delta.app (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                    ((restrict R A).obj (Q.obj N)))))) ∧
      (∀ M : E,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (c.app M) ≫ (gamma M).hom =
          (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (sigma M).hom ≫
            (L M).localizedComparison i) := by
  classical
  let V := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have hsp (M : E) : IsIso ((source R A B i).map (pi.app M)) := by
    have := hpi M
    exact source_isIso R A B i _
  let eB (M : E) : V.obj (S.obj M) ≅ V.obj ((L M).cohomology i) :=
    eS.app M ≪≫ (asIso ((source R A B i).map (pi.app M))).symm ≪≫
      (sourceIso R B (L M).derived (L M).counit (L M).universal i).app
        ((restrict R A).obj (Q.obj M)) ≪≫ ((L M).cohomologyIso i).symm
  have hB (M : E) (a : A) :
      V.map ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (S.obj M)) ≫
        (eB M).hom =
      (eB M).hom ≫ V.map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 ((L M).cohomology i)) := by
    apply (cancel_mono ((L M).cohomologyIso i).hom).1
    have hs : V.map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (S.obj M)) ≫
          eS.hom.app M = eS.hom.app M ≫ (source R A B i).map (a • 𝟙 (U.obj M)) := by
      ext x
      exact hS M a x
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [(L M).cohomologyIso_smul i a]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hs]
    simp only [Category.assoc]
    erw [scalar_inv_naturality_assoc A (source R A B i) (pi.app M) a]
    congr 2
    exact ((isoWhiskerLeft (restrict R A)
      (sourceIso R B (L M).derived (L M).counit (L M).universal i)).hom.naturality
        (a • 𝟙 (Q.obj M)))
  have hlift (M : E) : ∃ sigma : S.obj M ≅ (L M).cohomology i,
      V.map sigma.hom = (eB M).hom :=
    tensorIsoLift R A B _ _ (eB M) fun a x ↦ ConcreteCategory.congr_hom (hB M a) x
  choose sigma hsigma using hlift
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) i
  have htp (M : E) : IsIso ((target R A B i).map (pi.app M)) := by
    have := hpi M
    exact target_isIso R A B i _
  have htQ (M : E) : IsIso ((targetH R A B i).app (Q.obj M)) :=
    targetH_isIso R A B i _ (hQ M)
  let tB (M : E) : V.obj (T.obj M) ≅ V.obj (F.obj (Q.obj M)) :=
    eT.app M ≪≫ (asIso ((target R A B i).map (pi.app M))).symm ≪≫
      asIso ((targetH R A B i).app (Q.obj M))
  have htB (M : E) (a : A) :
      V.map ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (T.obj M)) ≫
        (tB M).hom =
      (tB M).hom ≫ V.map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (F.obj (Q.obj M))) := by
    have ht : V.map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (T.obj M)) ≫
          eT.hom.app M = eT.hom.app M ≫ (target R A B i).map (a • 𝟙 (U.obj M)) := by
      ext x
      exact hT M a x
    dsimp only [tB, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_inv, asIso_hom]
    rw [← Category.assoc, ht]
    simp only [Category.assoc]
    erw [scalar_inv_naturality_assoc A (target R A B i) (pi.app M) a]
    congr 2
    have hn := (targetH R A B i).naturality (a • 𝟙 (Q.obj M))
    change (target R A B i).map (a • 𝟙 (Q.obj M)) ≫ _ =
      _ ≫ V.map (HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
          ).map (a • 𝟙 (Q.obj M))) i) at hn
    rw [extensionH_scalar] at hn
    exact hn
  have htlift (M : E) : ∃ tau : T.obj M ≅ F.obj (Q.obj M),
      V.map tau.hom = (tB M).hom :=
    tensorIsoLift R A B _ _ (tB M) fun a x ↦ ConcreteCategory.congr_hom (htB M a) x
  choose tau htau using htlift
  have hpS : IsIso (Functor.whiskerRight pi (source R A B i)) :=
    (NatTrans.isIso_iff_isIso_app _).2 hsp
  have hpT : IsIso (Functor.whiskerRight pi (target R A B i)) :=
    (NatTrans.isIso_iff_isIso_app _).2 htp
  have htauNat (M N : E) (g : M ⟶ N) :
      T.map g ≫ (tau N).hom = (tau M).hom ≫ F.map (Q.map g) := by
    apply V.map_injective
    simp only [Functor.map_comp, htau]
    dsimp only [tB, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_inv, asIso_hom]
    have h1 := eT.hom.naturality g
    have h2 := (asIso (Functor.whiskerRight pi (target R A B i))).inv.naturality g
    simp only [asIso_inv, NatIso.isIso_inv_app, Functor.whiskerRight_app] at h2
    have h3 := (targetH R A B i).naturality (Q.map g)
    dsimp only [Functor.comp_map] at h1 h2 h3
    erw [← Category.assoc, h1]
    simp only [Category.assoc]
    erw [reassoc_of% h2, h3]
    rfl
  have hsigmaFac (M : E) : V.map (sigma M).hom ≫ ((L M).cohomologyIso i).hom =
      eS.hom.app M ≫ inv ((source R A B i).map (pi.app M)) ≫
        (sourceIso R B (L M).derived (L M).counit (L M).universal i).hom.app
          ((restrict R A).obj (Q.obj M)) := by
    rw [hsigma]
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hctau (M : E) : c.app M ≫ (tau M).hom =
      (sigma M).hom ≫ (L M).comparison i := by
    apply V.map_injective
    simp only [Functor.map_comp, htau]
    dsimp only [V]
    erw [model_comparison R A B D (Q.obj M) (L M) i]
    rw [← Category.assoc, hsigmaFac]
    simp only [Category.assoc]
    erw [sourceIso_fac_assoc R B (L M).derived (L M).counit (L M).universal i
      ((restrict R A).obj (Q.obj M)) ((ordinaryH R A B i).hom.app (Q.obj M))]
    dsimp only [tB, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_inv, asIso_hom]
    have hcm := congrArg (fun t ↦ t.app M) hc
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hcm
    rw [← Category.assoc, hcm]
    simp only [Category.assoc]
    erw [inverse_naturality_assoc (comparison R A B i) (pi.app M)]
    rw [comparison_targetH]
  let f := algebraMap A (A ⊗[R] B)
  let d := algebraMap (A ⊗[R] B) D
  let EL := ModuleCat.extendScalars d
  let FD := (ModuleCat.extendScalars (d.comp f)).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i
  let lambda (M : E) : EL.obj (F.obj (Q.obj M)) ⟶ FD.obj (Q.obj M) :=
    localHom f d (Q.obj M) (L M).ordinaryToLocalized i
  have hlambda (M : E) : IsIso (lambda M) :=
    ModuleCat.flatScalarExtensionHomologyAdjunct_isIso f d rfl
      (RingHom.flat_algebraMap_iff.mp hf) (Q.obj M) (L M).ordinaryToLocalized
        (L M).ordinaryToLocalized_tmul i
  let gamma (M : E) := EL.mapIso (tau M) ≪≫ asIso (lambda M)
  refine ⟨sigma, gamma, ?_, ?_, ?_⟩
  · intro M N g
    have hln := localHom_naturality f d (Q.obj M) (Q.obj N) (Q.map g)
      (L M).ordinaryToLocalized (L N).ordinaryToLocalized
      (L M).ordinaryToLocalized_tmul (L N).ordinaryToLocalized_tmul i
    change EL.map (T.map g) ≫ (EL.map (tau N).hom ≫ lambda N) =
      (EL.map (tau M).hom ≫ lambda M) ≫ FD.map (Q.map g)
    rw [← Category.assoc, ← EL.map_comp, htauNat, EL.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ EL.map (tau M).hom ≫ z) hln
  · intro M N g
    obtain ⟨delta, gmap, hdelta, hmap⟩ := exists_baseDerivedTensorCohomologyModelMap R A B D
      (Q.obj M) (Q.obj N) (Q.map g) (L M) (L N) i
    refine ⟨delta, hdelta, ?_⟩
    apply (cancel_epi (V.map (sigma M).hom)).1
    change V.map (sigma M).hom ≫
      V.map ((sigma M).inv ≫ S.map g ≫ (sigma N).hom) ≫
        ((L N).cohomologyIso i).hom = _
    simp only [V.map_comp, Category.assoc]
    rw [← V.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [hsigmaFac N, ← Category.assoc (V.map (sigma M).hom), hsigmaFac M]
    have h1 := eS.hom.naturality g
    have h2 := (asIso (Functor.whiskerRight pi (source R A B i))).inv.naturality g
    simp only [asIso_inv, NatIso.isIso_inv_app, Functor.whiskerRight_app] at h2
    dsimp only [Functor.comp_map] at h1 h2
    erw [← Category.assoc, h1]
    simp only [Category.assoc]
    erw [reassoc_of% h2]
    rw [← sourceIso_delta R B (L M).derived (L N).derived (L M).counit (L N).counit
      (L M).universal (L N).universal delta hdelta i ((restrict R A).obj (Q.obj N))]
    have hn := (isoWhiskerLeft (restrict R A)
      (sourceIso R B (L M).derived (L M).counit (L M).universal i)).hom.naturality (Q.map g)
    dsimp only [Functor.comp_map, Functor.whiskerLeft_app] at hn
    erw [reassoc_of% hn]
    rfl
  · intro M
    change EL.map (c.app M) ≫ (EL.map (tau M).hom ≫ lambda M) =
      EL.map (sigma M).hom ≫ (L M).localizedComparison i
    rw [← Category.assoc, ← EL.map_comp, hctau, EL.map_comp, Category.assoc]
    congr 1
    let adj := ModuleCat.extendRestrictScalarsAdj d
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    dsimp only [lambda, localHom, adj, F, FD, f, d]
    erw [Equiv.apply_symm_apply]
    simpa only [Adjunction.homEquiv_unit] using ((L M).localized_eq i).symm

end RingTensorCohomology
