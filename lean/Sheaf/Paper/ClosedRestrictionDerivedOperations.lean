/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparisonAux
import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Closed restriction and ordinary derived operations

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), Stacks Tags 09AA, 0BK6 and 015F;
the simultaneous compatibility is the agent assembly recorded in the DAG
(blueprint: lem-sfb-closed-restriction-derived-operations).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

universe uA uB vA vB wA wB

private theorem rightDerived_preservesProducts
    {J : Type*} {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [HasLimitsOfShape (Discrete J) A] [HasLimitsOfShape (Discrete J) B]
    [HasExactLimitsOfShape (Discrete J) B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete J) F] :
    PreservesLimitsOfShape (Discrete J) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : J → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : J) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : J) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := limit.cone (Discrete.functor I)
    have : P.pt.IsKInjective :=
      CochainComplex.isKInjective_of_isLimitFan (limit.isLimit (Discrete.functor I))
    have hPL : IsLimit (DerivedCategory.Q.mapCone P) :=
      (Fan.isLimitMapConeEquiv DerivedCategory.Q I P).symm
        (DerivedCategory.isLimitFanMkQObjOfIsKInjective
          (limit.isLimit (Discrete.functor I)))
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (limit.isLimit (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun n ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c)
      (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _


private theorem boundedResolution
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian A] :
    ∃ (I : CochainComplex.Plus A ⥤ CochainComplex.Plus A)
      (α : CochainComplex.Plus.ι A ⟶ I ⋙ CochainComplex.Plus.ι A),
      (∀ K, QuasiIso (α.app K)) ∧
      (∀ K, (I.obj K).obj.IsKInjective) ∧
      (∀ K a, K.obj.IsStrictlyGE a → (I.obj K).obj.IsStrictlyGE a) := by
  let S := HomologicalComplex.single A (.up ℤ) 0
  let R := CochainComplex.kInjectiveResolutionFunctor A
  let V := HomologicalComplex.eval A (.up ℤ) 0
  let J := S ⋙ R ⋙ V
  let η : 𝟭 A ⟶ J :=
    (HomologicalComplex.singleCompEvalIsoSelf A (.up ℤ) 0).inv ≫
      Functor.whiskerRight (Functor.whiskerLeft S (CochainComplex.toKInjectiveResolution A)) V
  have hη (M : A) : Mono (η.app M) := by
    have := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A (S.obj M)).1
    dsimp [η]
    infer_instance
  have hJ (M : A) : Injective (J.obj M) := by
    change Injective (((CochainComplex.kInjectiveResolutionFunctor A).obj
      (S.obj M)).X 0)
    exact CochainComplex.injective_kInjectiveResolutionFunctor_obj_X (S.obj M) 0
  obtain ⟨I, α, hα, hI, hbound⟩ :=
    CochainComplex.exists_functorial_bounded_injective_resolution J η hη hJ
  refine ⟨I, α, hα, ?_, hbound⟩
  intro K
  obtain ⟨a, ha⟩ := (I.obj K).property
  have := hI K
  exact CochainComplex.isKInjective_of_injective (I.obj K).obj a

private def chainUnit {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

private theorem boundedSectionModel
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive]
    (I : CochainComplex.Plus A ⥤ CochainComplex.Plus A)
    (α : CochainComplex.Plus.ι A ⟶ I ⋙ CochainComplex.Plus.ι A)
    (hα : ∀ K, QuasiIso (α.app K)) (hI : ∀ K, (I.obj K).obj.IsKInjective) :
    ∃ e : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅
        I ⋙ CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      ∀ K, e.hom.app K = F.rightDerivedFunctor.map (DerivedCategory.Q.map (α.app K)) ≫
        (F.rightDerivedFunctorObjQIso (I.obj K).obj).hom := by
  let (K : CochainComplex.Plus A) : QuasiIso (α.app K) := hα K
  let (K : CochainComplex.Plus A) : (I.obj K).obj.IsKInjective := hI K
  let (K : CochainComplex.Plus A) : IsIso (F.rightDerivedFunctorUnitQ (I.obj K).obj) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have : IsIso (Functor.whiskerRight α DerivedCategory.Q) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    change IsIso (DerivedCategory.Q.map (α.app K))
    infer_instance
  let q : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ≅
      I ⋙ CochainComplex.Plus.ι A ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight α DerivedCategory.Q)
  have : IsIso (Functor.whiskerLeft (I ⋙ CochainComplex.Plus.ι A) (chainUnit F)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    change IsIso (F.rightDerivedFunctorUnitQ (I.obj K).obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let ν : I ⋙ CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ≅ I ⋙ CochainComplex.Plus.ι A ⋙
        DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    asIso (Functor.whiskerLeft (I ⋙ CochainComplex.Plus.ι A) (chainUnit F))
  refine ⟨Functor.isoWhiskerRight q F.rightDerivedFunctor ≪≫
    Functor.associator _ _ _ ≪≫ ν.symm, ?_⟩
  intro K
  simp only [q, ν, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, asIso_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Category.id_comp, Iso.symm_hom, asIso_inv,
    NatIso.isIso_inv_app, Functor.whiskerLeft_app]
  change _ ≫ inv (F.rightDerivedFunctorUnitQ (I.obj K).obj) = _
  simp only [F.rightDerivedFunctorUnitQ_eq, IsIso.Iso.inv_inv]

private theorem continuityRepresentatives
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{vA} A] [HasDerivedCategory.{vB} B]
    {J : Type*} [Category J] [IsFiltered J]
    [HasColimitsOfShape J A] [HasColimitsOfShape J B] [HasExactColimitsOfShape J B]
    (D : J ⥤ CochainComplex A ℤ) (a : ℤ) (ha : ∀ i, (D.obj i).IsStrictlyGE a)
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : J ⥤ CochainComplex B ℤ) (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (colimit D)) ≅ DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const J).obj L)
    (hι : ∀ i, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map (colimit.ι D i)) ≫ ε.hom) :
    IsIso (DerivedCategory.Q.map (colimit.desc P (Cocone.mk L ι))) := by
  let (i : J) : IsIso ((D.obj i).πTruncGE a) :=
    (CochainComplex.isIso_πTruncGE_iff _ _).2 (ha i)
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have : IsIso π := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun i ↦ ?_)
    change IsIso ((D.obj i).πTruncGE a)
    infer_instance
  let k := colimit.desc D (AlgebraicGeometry.ProEtale.condensedContinuityCocone D a)
  have hk : k = colimMap π := rfl
  have : IsIso k := by rw [hk]; infer_instance
  let ε' := (F.mapIso (asIso (DerivedCategory.Q.map k))).symm ≪≫ ε
  have hι' (i) : e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map
        ((AlgebraicGeometry.ProEtale.condensedContinuityCocone D a).ι.app i)) ≫ ε'.hom := by
    rw [hι]
    have hkι := colimit.ι_desc
      (AlgebraicGeometry.ProEtale.condensedContinuityCocone D a) i
    change colimit.ι D i ≫ k = _ at hkι
    simp only [ε', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
    rw [← hkι, Functor.map_comp, Functor.map_comp]
    simp only [Functor.map_inv]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have := AlgebraicGeometry.ProEtale.condensedContinuityComparison_representatives
    D a F h P L e ε' ι hι'
  infer_instance

private theorem derived_hasProduct {J : Type*}
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasLimitsOfShape (Discrete J) A]
    (K : J → DerivedCategory A) : HasProduct K := by
  classical
  choose I hI he using fun j ↦ DerivedCategory.exists_iso_Q_obj_of_isKInjective (K j)
  have : ∀ j, (I j).IsKInjective := hI
  let e : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
    Discrete.natIso (fun j ↦ (Classical.choice (he j.as)).symm)
  let c := (Cone.postcompose e.hom).obj (DerivedCategory.Q.mapCone
    (limit.cone (Discrete.functor I)))
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv e _).symm
    ((Fan.isLimitMapConeEquiv DerivedCategory.Q I _).symm
      (DerivedCategory.isLimitFanMkQObjOfIsKInjective (productIsProduct I)))
  exact ⟨⟨c, hc⟩⟩

private theorem pullback_commShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : A ⥤ C) (G : B ⥤ C) [F.Additive] [G.Additive]
    (β : F ⟶ E ⋙ G) : NatTrans.CommShift (Functor.rightDerivedPullback E β) ℤ := by
  have := AlgebraicGeometry.RingedSpace.unit_commShift_all F
  have := AlgebraicGeometry.RingedSpace.unit_commShift_all G
  have : NatTrans.CommShift (Functor.rightDerivedPullbackAux E β) ℤ := by
    dsimp only [Functor.rightDerivedPullbackAux]
    have : NatTrans.CommShift
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G)) (.up ℤ)).inv ℤ :=
      NatTrans.CommShift.of_iso_inv _ _
    have : NatTrans.CommShift E.mapDerivedCategoryFactorsh.inv ℤ :=
      NatTrans.CommShift.of_iso_inv _ _
    infer_instance
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal)
      F.rightDerivedFunctorUnit) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp
    infer_instance
  have : NatTrans.CommShift (F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedPullback E β)) ℤ := by
    rw [Functor.rightDerivedPullback, Functor.rightDerived_fac]
    infer_instance
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh F.rightDerivedFunctorUnit _

private theorem derivedStructures
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : A ⥤ C) (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.rightDerivedFunctor.Additive ∧
      (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).Additive ∧
      F.rightDerivedFunctor.IsTriangulated ∧
      (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsTriangulated :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem twoResolutionFormula
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : A ⥤ C) (G : B ⥤ C) [F.Additive] [G.Additive] (β : F ⟶ E ⋙ G)
    (K I : CochainComplex A ℤ) [I.IsKInjective] (s : K ⟶ I) [QuasiIso s]
    (H : CochainComplex B ℤ) [H.IsKInjective]
    (j : (E.mapHomologicalComplex (.up ℤ)).obj I ⟶ H) [QuasiIso j] :
    (Functor.rightDerivedPullback E β).app (DerivedCategory.Q.obj K) ≫
      G.rightDerivedFunctor.map
        (E.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
          ((E.mapHomologicalComplex (.up ℤ)).map s ≫ j)) ≫
      (G.rightDerivedFunctorObjQIso H).hom =
    F.rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
      (F.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex β (.up ℤ)).app I ≫
          (G.mapHomologicalComplex (.up ℤ)).map j) := by
  have h := Functor.rightDerivedPullback_app_Q_obj E β I H j
  have hn := (Functor.rightDerivedPullback E β).naturality (DerivedCategory.Q.map s)
  dsimp only [Functor.comp_map] at hn
  have hf : E.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((E.mapHomologicalComplex (.up ℤ)).map s ≫ j) =
      E.mapDerivedCategory.map (DerivedCategory.Q.map s) ≫
        E.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j := by
    rw [Functor.map_comp, ← Category.assoc]
    have hh := E.mapDerivedCategoryFactors.hom.naturality s
    dsimp only [Functor.comp_map] at hh
    rw [← hh, Category.assoc]
  rw [hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hh := congrArg
    (fun z ↦ F.rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫ z ≫
      (G.rightDerivedFunctorObjQIso H).hom) h
  simpa only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

private theorem productsNaturality
    {A B : Type*} [Category A] [Category B] {J : Type*}
    (F G : A ⥤ B) [PreservesLimitsOfShape (Discrete J) F]
    [PreservesLimitsOfShape (Discrete J) G] (τ : F ⟶ G)
    (K : J → A) [HasLimit (Discrete.functor K)] :
    ∃ c : Fan K, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (F.mapCone c)) ∧
      Nonempty (IsLimit (G.mapCone c)) ∧
      ∀ (cF : Cone (Discrete.functor K ⋙ F)) (hF : IsLimit cF)
        (cG : Cone (Discrete.functor K ⋙ G)) (hG : IsLimit cG),
        hF.lift (F.mapCone c) ≫ hG.lift
          ((Cone.postcompose (Functor.whiskerLeft (Discrete.functor K) τ)).obj cF) =
        τ.app c.pt ≫ hG.lift (G.mapCone c) := by
  let c := limit.cone (Discrete.functor K)
  refine ⟨c, ⟨limit.isLimit _⟩, ⟨isLimitOfPreserves _ (limit.isLimit _)⟩,
    ⟨isLimitOfPreserves _ (limit.isLimit _)⟩, ?_⟩
  intro cF hF cG hG
  apply hG.hom_ext
  intro j
  simp only [Category.assoc, hG.fac]
  change hF.lift (F.mapCone c) ≫ (cF.π.app j ≫ τ.app (K j.as)) =
    τ.app c.pt ≫ G.map (c.π.app j)
  rw [← Category.assoc, hF.fac]
  exact τ.naturality (c.π.app j)

private theorem triangleMap
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (Δ : Triangle A) :
    ∃ r : F.mapTriangle.obj Δ ⟶ G.mapTriangle.obj Δ,
      r.hom₁ = τ.app Δ.obj₁ ∧ r.hom₂ = τ.app Δ.obj₂ ∧ r.hom₃ = τ.app Δ.obj₃ := by
  refine ⟨{ hom₁ := τ.app Δ.obj₁
            hom₂ := τ.app Δ.obj₂
            hom₃ := τ.app Δ.obj₃
            comm₁ := τ.naturality Δ.mor₁
            comm₂ := τ.naturality Δ.mor₂
            comm₃ := ?_ }, rfl, rfl, rfl⟩
  change (F.map Δ.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) ≫
      (shiftFunctor B (1 : ℤ)).map (τ.app Δ.obj₁) =
    τ.app Δ.obj₃ ≫ G.map Δ.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app Δ.obj₁
  rw [Category.assoc, NatTrans.shift_app_comm, NatTrans.naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem boundedRestrictionModel
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian A] [IsGrothendieckAbelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : A ⥤ C) (G : B ⥤ C) [F.Additive] [G.Additive]
    (β : F ⟶ E ⋙ G)
    {J : Type*} [SmallCategory J] [HasColimitsOfShape J A]
    (D : J ⥤ CochainComplex A ℤ)
    (a : ℤ) (ha : ∀ i, (D.obj i).IsStrictlyGE a) :
  ∃ (P R : J ⥤ CochainComplex C ℤ)
    (L M : CochainComplex C ℤ)
    (eF : D ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅ P ⋙ DerivedCategory.Q)
    (eG : D ⋙ DerivedCategory.Q ⋙ (E.mapDerivedCategory ⋙ G.rightDerivedFunctor) ≅
      R ⋙ DerivedCategory.Q)
    (εF : F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (colimit D)) ≅
      DerivedCategory.Q.obj L)
    (εG : (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).obj (DerivedCategory.Q.obj (colimit D)) ≅
      DerivedCategory.Q.obj M)
    (α : P ⟶ (Functor.const J).obj L) (γ : R ⟶ (Functor.const J).obj M)
    (η : P ⟶ R) (m : L ⟶ M),
    (∀ i : J, (P.obj i).IsStrictlyGE a ∧ (R.obj i).IsStrictlyGE a) ∧
    L.IsStrictlyGE a ∧ M.IsStrictlyGE a ∧
    (∀ i : J, eF.hom.app i ≫ DerivedCategory.Q.map (α.app i) =
      F.rightDerivedFunctor.map (DerivedCategory.Q.map (colimit.ι D i)) ≫ εF.hom) ∧
    (∀ i : J, eG.hom.app i ≫ DerivedCategory.Q.map (γ.app i) =
      (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).map
        (DerivedCategory.Q.map (colimit.ι D i)) ≫ εG.hom) ∧
    (∀ i : J, eF.hom.app i ≫ DerivedCategory.Q.map (η.app i) =
      (Functor.rightDerivedPullback E β).app (DerivedCategory.Q.obj (D.obj i)) ≫ eG.hom.app i) ∧
    (εF.hom ≫ DerivedCategory.Q.map m =
      (Functor.rightDerivedPullback E β).app (DerivedCategory.Q.obj (colimit D)) ≫ εG.hom) ∧
    (∀ i : J, η.app i ≫ γ.app i = α.app i ≫ m) := by
  classical
  obtain ⟨I, α, hα, hI, hbI⟩ := boundedResolution (A := A)
  obtain ⟨H, j, hj, hH, hbH⟩ := boundedResolution (A := B)
  obtain ⟨eF, heF⟩ := boundedSectionModel F I α hα hI
  obtain ⟨eH, heH⟩ := boundedSectionModel G H j hj hH
  let (K : CochainComplex.Plus A) : QuasiIso (α.app K) := hα K
  let (K : CochainComplex.Plus A) : (I.obj K).obj.IsKInjective := hI K
  let (K : CochainComplex.Plus B) : QuasiIso (j.app K) := hj K
  let (K : CochainComplex.Plus B) : (H.obj K).obj.IsKInjective := hH K
  let P := I ⋙ CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (.up ℤ)
  let R := I ⋙ E.mapCochainComplexPlus ⋙ H ⋙ CochainComplex.Plus.ι B ⋙
    G.mapHomologicalComplex (.up ℤ)
  have : IsIso (Functor.whiskerRight α DerivedCategory.Q) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    change IsIso (DerivedCategory.Q.map (α.app K))
    infer_instance
  let q : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ≅
      I ⋙ CochainComplex.Plus.ι A ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight α DerivedCategory.Q)
  let eG : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ⋙
      (E.mapDerivedCategory ⋙ G.rightDerivedFunctor) ≅ R ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight q (E.mapDerivedCategory ⋙ G.rightDerivedFunctor) ≪≫
      Functor.isoWhiskerLeft (I ⋙ CochainComplex.Plus.ι A)
        (Functor.isoWhiskerRight E.mapDerivedCategoryFactors G.rightDerivedFunctor) ≪≫
      Functor.isoWhiskerLeft (I ⋙ E.mapCochainComplexPlus) eH
  let η : P ⟶ R :=
    Functor.whiskerLeft (I ⋙ CochainComplex.Plus.ι A)
      (NatTrans.mapHomologicalComplex β (.up ℤ)) ≫
    Functor.whiskerRight (Functor.whiskerLeft (I ⋙ E.mapCochainComplexPlus) j)
      (G.mapHomologicalComplex (.up ℤ))
  have heρ (K : CochainComplex.Plus A) :
      eF.hom.app K ≫ DerivedCategory.Q.map (η.app K) =
        (Functor.rightDerivedPullback E β).app (DerivedCategory.Q.obj K.obj) ≫ eG.hom.app K := by
    rw [heF]
    dsimp only [eG, q, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    rw [heH]
    dsimp only [η, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have h := Functor.rightDerivedPullback_app_Q_obj E
      β (I.obj K).obj (H.obj
        (E.mapCochainComplexPlus.obj (I.obj K))).obj
      (j.app (E.mapCochainComplexPlus.obj (I.obj K)))
    simp only [Category.assoc]
    change F.rightDerivedFunctor.map (DerivedCategory.Q.map (α.app K)) ≫
        (F.rightDerivedFunctorObjQIso (I.obj K).obj).hom ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex β
                (.up ℤ)).app (I.obj K).obj ≫
              (G.mapHomologicalComplex (.up ℤ)).map
                (j.app (E.mapCochainComplexPlus.obj (I.obj K)))) =
      (Functor.rightDerivedPullback E β).app (DerivedCategory.Q.obj K.obj) ≫
        G.rightDerivedFunctor.map
          (E.mapDerivedCategory.map (DerivedCategory.Q.map (α.app K))) ≫
        G.rightDerivedFunctor.map (E.mapDerivedCategoryFactors.hom.app (I.obj K).obj) ≫
        G.rightDerivedFunctor.map
          (DerivedCategory.Q.map (j.app (E.mapCochainComplexPlus.obj (I.obj K)))) ≫
        (G.rightDerivedFunctorObjQIso
          (H.obj (E.mapCochainComplexPlus.obj (I.obj K))).obj).hom
    have hn := (Functor.rightDerivedPullback E β).naturality (DerivedCategory.Q.map (α.app K))
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hh := congrArg
      (fun z ↦ F.rightDerivedFunctor.map (DerivedCategory.Q.map (α.app K)) ≫ z ≫
        (G.rightDerivedFunctorObjQIso
          (H.obj (E.mapCochainComplexPlus.obj (I.obj K))).obj).hom) h
    simpa only [Functor.map_comp, Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hh.symm
  let D' : J ⥤ CochainComplex.Plus A :=
    { obj := fun i ↦ ⟨D.obj i, a, ha i⟩
      map := fun f ↦ ObjectProperty.homMk (D.map f) }
  have hcol : (colimit D).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n)
      (colimit.isColimit D)).isZero_pt
      (Functor.isZero _ fun i ↦ (D.obj i).isZero_of_isStrictlyGE a n hn)
  let C : CochainComplex.Plus A := ⟨colimit D, a, hcol⟩
  let δ : D' ⟶ (Functor.const J).obj C :=
    { app := fun i ↦ ObjectProperty.homMk (colimit.ι D i)
      naturality := fun i k f ↦ by
        ext : 1
        change D.map f ≫ colimit.ι D k = colimit.ι D i ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w D f }
  refine ⟨D' ⋙ P, D' ⋙ R, P.obj C, R.obj C,
    Functor.isoWhiskerLeft D' eF, Functor.isoWhiskerLeft D' eG,
    eF.app C, eG.app C,
    Functor.whiskerRight δ P ≫ (Functor.constComp J C P).hom,
    Functor.whiskerRight δ R ≫ (Functor.constComp J C R).hom,
    Functor.whiskerLeft D' η, η.app C, ?_, ?_, ?_, ?_, ?_, ?_, heρ C, ?_⟩
  · intro i
    have h₁ := hbI (D'.obj i) a (ha i)
    have h₂ := hbH (E.mapCochainComplexPlus.obj (I.obj (D'.obj i))) a
      (by dsimp [Functor.mapCochainComplexPlus]; infer_instance)
    exact ⟨by dsimp [P]; infer_instance, by dsimp [R]; infer_instance⟩
  · have := hbI C a hcol
    dsimp [P]
    infer_instance
  · have := hbI C a hcol
    have := hbH (E.mapCochainComplexPlus.obj (I.obj C)) a
      (by dsimp [Functor.mapCochainComplexPlus]; infer_instance)
    dsimp [R]
    infer_instance
  · intro i
    simpa [P, R, D', δ] using (eF.hom.naturality (δ.app i)).symm
  · intro i
    simpa [P, R, D', δ] using (eG.hom.naturality (δ.app i)).symm
  · intro i
    exact heρ (D'.obj i)
  · intro i
    simpa [P, R, D', δ] using (η.naturality (δ.app i)).symm


set_option backward.isDefEq.respectTransparency false in
private theorem pullbackContinuityRepresentatives
    {A : Type uA} {B : Type uB} {C : Type u}
    [Category.{vA} A] [Category.{vB} B] [Category.{wA} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{vA} A] [HasDerivedCategory.{vB} B]
    [HasDerivedCategory.{wA} C] [Abelian.HasKInjectiveResolutions B]
    {J : Type*} [Category J] [IsFiltered J]
    [HasColimitsOfShape J A] [HasColimitsOfShape J B] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesColimitsOfShape J E] (G : B ⥤ C) [G.Additive]
    (D : J ⥤ CochainComplex A ℤ) (a : ℤ)
    (ha : ∀ i, (D.obj i).IsStrictlyGE a)
    (h : ∀ q : ℤ, IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison
      (D ⋙ E.mapHomologicalComplex (.up ℤ)) a
      (DerivedCategory.Q ⋙ G.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor C q)))
    (R : J ⥤ CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (eG : D ⋙ DerivedCategory.Q ⋙ (E.mapDerivedCategory ⋙ G.rightDerivedFunctor) ≅
      R ⋙ DerivedCategory.Q)
    (εG : (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).obj
      (DerivedCategory.Q.obj (colimit D)) ≅ DerivedCategory.Q.obj M)
    (γ : R ⟶ (Functor.const J).obj M)
    (hγ : ∀ i, eG.hom.app i ≫ DerivedCategory.Q.map (γ.app i) =
      (E.mapDerivedCategory ⋙ G.rightDerivedFunctor).map
        (DerivedCategory.Q.map (colimit.ι D i)) ≫ εG.hom) :
    IsIso (DerivedCategory.Q.map (colimit.desc R (Cocone.mk M γ))) := by
  let E' := E.mapHomologicalComplex (.up ℤ)
  let F := G.rightDerivedFunctor
  let κ := preservesColimitIso E' D
  let e : (D ⋙ E') ⋙ DerivedCategory.Q ⋙ F ≅ R ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft D
      (Functor.isoWhiskerRight E.mapDerivedCategoryFactors F).symm ≪≫ eG
  let ε : F.obj (DerivedCategory.Q.obj (colimit (D ⋙ E'))) ≅ DerivedCategory.Q.obj M :=
    F.mapIso (DerivedCategory.Q.mapIso κ.symm) ≪≫
      (F.mapIso (E.mapDerivedCategoryFactors.app (colimit D))).symm ≪≫ εG
  have hb (i : J) : CochainComplex.IsStrictlyGE ((D ⋙ E').obj i) a := by
    have := ha i
    dsimp [E']
    infer_instance
  apply continuityRepresentatives (D ⋙ E') a hb F h R M e ε γ
  intro i
  dsimp only [e, ε, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.mapIso_hom]
  rw [Category.assoc, hγ]
  have hκ := ι_preservesColimitIso_inv E' D i
  have hf := E.mapDerivedCategoryFactors.inv.naturality (colimit.ι D i)
  dsimp only [Functor.comp_map] at hf
  have heq : E.mapDerivedCategoryFactors.inv.app (D.obj i) ≫
      E.mapDerivedCategory.map (DerivedCategory.Q.map (colimit.ι D i)) =
      DerivedCategory.Q.map (colimit.ι (D ⋙ E') i) ≫
        DerivedCategory.Q.map κ.inv ≫ E.mapDerivedCategoryFactors.inv.app (colimit D) := by
    rw [← hf, ← hκ, Functor.map_comp, Category.assoc]
  simpa only [F, Functor.comp_map, Functor.map_comp, Category.assoc,
    Functor.mapIso_inv, Iso.app_inv, Functor.comp_obj] using
    congrArg (fun z ↦ F.map z ≫ εG.hom) heq

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {T₀ T : Scheme.{u}} (t : T₀ ⟶ T)

-- Prefer the existing shape-level colimit instance to repeated degreewise searches.
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape

private theorem moduleProductsExact (V : Scheme.{u}) (J : Type (u + 1)) :
    HasExactLimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) := by
  let E := CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology V) (condensedRingObj Λ V)
  have h : HasExactLimitsOfShape (Discrete J)
      (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology V)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology V) (condensedRingObj Λ V)))) :=
    Scheme.ProEt.products_exact.{u, u, u + 1} V _ J
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete J) E.symm

private theorem pullback_preservesProducts [IsClosedImmersion t] (J : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete J) (upperStar Λ t) := by
  have := (Scheme.proEtale_immersion_inverseImage_preservesLimits t).2.1
  have : PreservesLimitsOfShape (Discrete J) (ProEtale.upperStar Ab.{u + 1} t) :=
    preservesLimitsOfShape_of_natIso
      ((Scheme.proEtaleSheafAdjunction t Ab.{u + 1}).leftAdjointUniq
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} t))
  let G := ProEtale.upperStar Ab.{u + 1} t
  let V : Mod (Sheaf (Scheme.ProEt.topology T₀) Ab.{u + 1})
      (G.obj (condensedRingObj Λ T)) ⥤
      Sheaf (Scheme.ProEt.topology T₀) Ab.{u + 1} :=
    Mod.forget (G.obj (condensedRingObj Λ T))
  have : PreservesLimitsOfShape (Discrete J)
      (G.mapMod (condensedRingObj Λ T) ⋙ V) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete J) (Mod.forget _ ⋙ G))
  have : ReflectsLimitsOfShape (Discrete J) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete J) (G.mapMod (condensedRingObj Λ T)) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ V
  have : PreservesLimitsOfShape (Discrete J)
      (Mod.extendScalars (condensedPullbackHom Λ t)) :=
    preservesLimitsOfShape_of_natIso (Mod.extendScalarsIsoComapInv
      (condensedPullbackHom Λ t)).symm
  unfold upperStar
  exact comp_preservesLimitsOfShape _ _

/-- Section restriction: the module adjunction unit, evaluated at the terminal object,
followed by restriction from its base change to the source terminal object. This is the
same underived map used by `supportedModelDerivedRestriction`, before its support-chain
precomposition. Source: Stacks 09AA and the DAG's actual restriction formula
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
def closedRestrictionSections :
    condensedModuleSections Λ T ⟶ upperStar Λ t ⋙ condensedModuleSections Λ T₀ :=
  Functor.whiskerRight (upperStarLowerStarAdjunction Λ t).unit
      (condensedModuleSections Λ T) ≫
    Functor.whiskerLeft (upperStar Λ t)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ T₀))
        ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift t (𝟙 T₀)
              ((Category.comp_id t).trans (Category.id_comp t).symm))
            (pullback.lift_snd _ _ _)).op))

/-- Phi is the existing total right derived functor of abelian-group-valued module
sections, without completion. Source: HRS Lemma 5.3(1), global-sections case
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
abbrev closedRestrictionPhi (V : Scheme.{u}) :=
  (condensedModuleSections Λ V).rightDerivedFunctor

/-- Psi is exact termwise module pullback followed by ordinary derived sections.
The coefficient identification is the existing `condensedPullbackHom` isomorphism in
`upperStar`. Source: Stacks 09AA and the DAG's definition of Psi
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
abbrev closedRestrictionPsi :=
  (upperStar Λ t).mapDerivedCategory ⋙ closedRestrictionPhi Λ T₀

/-- The actual restriction is the universal right-derived descent of section restriction.
This uses a second resolution after pullback and does not require preservation of
K-injectives. Source: Stacks 015F and the DAG's two-resolution formula
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
def closedRestrictionRho : closedRestrictionPhi Λ T ⟶ closedRestrictionPsi Λ t :=
  Functor.rightDerivedPullback (upperStar Λ t) (closedRestrictionSections Λ t)

/-- Product preservation with the actual projection-induced comparisons and the product
of the components of restriction. Arbitrary limiting cones avoid making new choices
of products. Source: Stacks 0BK6 and the product clauses of the DAG
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
def ClosedRestrictionProducts : Prop :=
  ∀ (J : Type (u + 1))
    (K : J → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))),
    ∃ c : Fan K, Nonempty (IsLimit c) ∧
      Nonempty (IsLimit ((closedRestrictionPhi Λ T).mapCone c)) ∧
      Nonempty (IsLimit ((closedRestrictionPsi Λ t).mapCone c)) ∧
      ∀ (cF : Cone (Discrete.functor K ⋙ closedRestrictionPhi Λ T))
        (hF : IsLimit cF)
        (cG : Cone (Discrete.functor K ⋙ closedRestrictionPsi Λ t))
        (hG : IsLimit cG),
        hF.lift ((closedRestrictionPhi Λ T).mapCone c) ≫
            hG.lift ((Cone.postcompose
              (Functor.whiskerLeft (Discrete.functor K) (closedRestrictionRho Λ t))).obj cF) =
          (closedRestrictionRho Λ t).app c.pt ≫
            hG.lift ((closedRestrictionPsi Λ t).mapCone c)

/-- Existence of a simultaneous bounded-below chain model for the filtered diagram,
its colimit and the actual restriction between their derived section complexes.
All identifications and cocone legs are normalized, so this cannot choose an arbitrary
arrow in place of restriction. Source: Stacks 0141 and the DAG's step 7
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
def HasClosedRestrictionFilteredModel
    {J : Type (u + 1)} [SmallCategory J]
    (D : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ) : Prop :=
  ∃ (P R : J ⥤ CochainComplex Ab.{u + 1} ℤ)
    (L M : CochainComplex Ab.{u + 1} ℤ)
    (eF : D ⋙ DerivedCategory.Q ⋙ closedRestrictionPhi Λ T ≅ P ⋙ DerivedCategory.Q)
    (eG : D ⋙ DerivedCategory.Q ⋙ closedRestrictionPsi Λ t ≅ R ⋙ DerivedCategory.Q)
    (εF : (closedRestrictionPhi Λ T).obj (DerivedCategory.Q.obj (colimit D)) ≅
      DerivedCategory.Q.obj L)
    (εG : (closedRestrictionPsi Λ t).obj (DerivedCategory.Q.obj (colimit D)) ≅
      DerivedCategory.Q.obj M)
    (α : P ⟶ (Functor.const J).obj L) (γ : R ⟶ (Functor.const J).obj M)
    (η : P ⟶ R) (m : L ⟶ M),
    (∀ i : J, (P.obj i).IsStrictlyGE a ∧ (R.obj i).IsStrictlyGE a) ∧
    L.IsStrictlyGE a ∧ M.IsStrictlyGE a ∧
    (∀ i : J, eF.hom.app i ≫ DerivedCategory.Q.map (α.app i) =
      (closedRestrictionPhi Λ T).map (DerivedCategory.Q.map (colimit.ι D i)) ≫ εF.hom) ∧
    (∀ i : J, eG.hom.app i ≫ DerivedCategory.Q.map (γ.app i) =
      (closedRestrictionPsi Λ t).map (DerivedCategory.Q.map (colimit.ι D i)) ≫ εG.hom) ∧
    (∀ i : J, eF.hom.app i ≫ DerivedCategory.Q.map (η.app i) =
      (closedRestrictionRho Λ t).app (DerivedCategory.Q.obj (D.obj i)) ≫ eG.hom.app i) ∧
    (εF.hom ≫ DerivedCategory.Q.map m =
      (closedRestrictionRho Λ t).app (DerivedCategory.Q.obj (colimit D)) ≫ εG.hom) ∧
    (∀ i : J, η.app i ≫ γ.app i = α.app i ≫ m)

set_option backward.isDefEq.respectTransparency false in
private theorem filteredModel
    {J : Type (u + 1)} [SmallCategory J]
    (D : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ) (ha : ∀ i, (D.obj i).IsStrictlyGE a) :
    HasClosedRestrictionFilteredModel Λ t D a := by
  exact boundedRestrictionModel (upperStar Λ t) (condensedModuleSections Λ T)
    (condensedModuleSections Λ T₀) (closedRestrictionSections Λ t) D a ha

/-- Filtered continuity on all normalized chain representatives, together with a
simultaneous bounded-below model in which the termwise colimit of a chain
representative of restriction is a chain representative of restriction at the colimit.
The two equations on cocone legs require the original cocone maps. Quantification over
all choices expresses independence of quasi-isomorphic replacements for the two
cocone-induced comparisons. The restriction square is asserted on the model of
`HasClosedRestrictionFilteredModel`, where it holds before localization: a chain
transformation is not determined by its derived components (phantom maps out of a
filtered colimit), so the square is not asserted for arbitrary chain lifts of rho.
No categorical colimit of arbitrary derived diagrams is substituted for a termwise
colimit of complexes. Source: HRS Lemma 5.3(1), representative form of continuity
(blueprint: lem-sfb-closed-restriction-derived-operations). -/
def ClosedRestrictionFilteredRepresentatives : Prop :=
  ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ), (∀ i : J, (D.obj i).IsStrictlyGE a) →
    HasClosedRestrictionFilteredModel Λ t D a ∧
    (∀ (P R : J ⥤ CochainComplex Ab.{u + 1} ℤ)
      (L M : CochainComplex Ab.{u + 1} ℤ)
      (eF : D ⋙ DerivedCategory.Q ⋙ closedRestrictionPhi Λ T ≅ P ⋙ DerivedCategory.Q)
      (eG : D ⋙ DerivedCategory.Q ⋙ closedRestrictionPsi Λ t ≅ R ⋙ DerivedCategory.Q)
      (εF : (closedRestrictionPhi Λ T).obj (DerivedCategory.Q.obj (colimit D)) ≅
        DerivedCategory.Q.obj L)
      (εG : (closedRestrictionPsi Λ t).obj (DerivedCategory.Q.obj (colimit D)) ≅
        DerivedCategory.Q.obj M)
      (α : P ⟶ (Functor.const J).obj L) (γ : R ⟶ (Functor.const J).obj M),
      (∀ i : J, eF.hom.app i ≫ DerivedCategory.Q.map (α.app i) =
        (closedRestrictionPhi Λ T).map (DerivedCategory.Q.map (colimit.ι D i)) ≫ εF.hom) →
      (∀ i : J, eG.hom.app i ≫ DerivedCategory.Q.map (γ.app i) =
        (closedRestrictionPsi Λ t).map (DerivedCategory.Q.map (colimit.ι D i)) ≫ εG.hom) →
      IsIso (DerivedCategory.Q.map (colimit.desc P (Cocone.mk L α))) ∧
      IsIso (DerivedCategory.Q.map (colimit.desc R (Cocone.mk M γ))))

set_option backward.isDefEq.respectTransparency false in
/-- The actual module-derived closed restriction respects triangles (including the
connecting arrow), all small products and uniformly bounded-below filtered colimits.
Its formula holds for every pair of K-injective resolutions, hence is independent
of both choices. There is no condition on the complementary open.

Source: HRS Lemma 5.3(1), Stacks 09AA, 0BK6, 05SE, 070Y and 015F; agent assembly
(blueprint: lem-sfb-closed-restriction-derived-operations).

Proof:
1. Use the internal-module/section-module equivalence to transfer exact products
from pro-etale module sheaves. The immersion limit theorem gives product-preserving
inverse image, and extension along the canonical coefficient isomorphism preserves
products. Pullback preserves colimits by its adjunction.
2. The existing `rightDerivedPullback_app_Q_obj` computes restriction on the two
K-injective resolutions. Naturality transports this formula along the first
quasi-isomorphism. The derived units commute with signed shifts, hence their
universal descent does as well. Naturality and the shift equation give the three
squares of the triangle morphism.
3. Products of K-injective complexes are K-injective. Sections preserve their
termwise product, and exact products in Ab identify its localization with the derived
product. Exact product-preserving pullback preserves derived products by the existing
`preservesLimitsOfShape_discrete_mapDerivedCategory`. Naturality at the projections
then proves the specified equality for rho, including the empty family.
4. Apply the normalized qcqs section-continuity theorem on T and T0. A common
termwise lower bound makes the good-truncation projection an isomorphism, including
at the colimit. Pullback commutes with the termwise colimit by its adjunction. These
identifications retain the original cocone legs and prove invertibility for every
normalized pair of representatives.
5. The degree-zero term of a functorial injective resolution of M[0] gives a monic
functorial injective embedding of M. The bounded injective-resolution theorem gives
functorial resolutions preserving every common lower bound. Apply it on T and T0.
Sections of these resolutions and the two-resolution restriction formula give the
simultaneous chain model. Its cocone maps come from functoriality at the original
colimit injections; naturality gives all four normalized derived equations and the
commuting chain square before localization. -/
theorem closed_restriction_derived_operations
    [IsClosedImmersion t] [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀] :
    (closedRestrictionPhi Λ T).Additive ∧ (closedRestrictionPsi Λ t).Additive ∧
    (closedRestrictionPhi Λ T).IsTriangulated ∧ (closedRestrictionPsi Λ t).IsTriangulated ∧
    NatTrans.CommShift (closedRestrictionRho Λ t) ℤ ∧
    (∀ (K I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
      [I.IsKInjective] (s : K ⟶ I) [QuasiIso s]
      (H : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology T₀) Ab.{u + 1}) (condensedRingObj Λ T₀)) ℤ)
      [H.IsKInjective]
      (j : ((upperStar Λ t).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ H)
      [QuasiIso j],
      (closedRestrictionRho Λ t).app (DerivedCategory.Q.obj K) ≫
          (closedRestrictionPhi Λ T₀).map
            ((upperStar Λ t).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map
                (((upperStar Λ t).mapHomologicalComplex (ComplexShape.up ℤ)).map s ≫ j)) ≫
          ((condensedModuleSections Λ T₀).rightDerivedFunctorObjQIso H).hom =
        (closedRestrictionPhi Λ T).map (DerivedCategory.Q.map s) ≫
          ((condensedModuleSections Λ T).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (closedRestrictionSections Λ t)
                (ComplexShape.up ℤ)).app I ≫
              ((condensedModuleSections Λ T₀).mapHomologicalComplex
                (ComplexShape.up ℤ)).map j)) ∧
    (∀ Δ : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))),
      Δ ∈ distTriang _ →
      ∃ r : (closedRestrictionPhi Λ T).mapTriangle.obj Δ ⟶
          (closedRestrictionPsi Λ t).mapTriangle.obj Δ,
        r.hom₁ = (closedRestrictionRho Λ t).app Δ.obj₁ ∧
        r.hom₂ = (closedRestrictionRho Λ t).app Δ.obj₂ ∧
        r.hom₃ = (closedRestrictionRho Λ t).app Δ.obj₃) ∧
    ClosedRestrictionProducts Λ t ∧ ClosedRestrictionFilteredRepresentatives Λ t := by
  obtain ⟨hF, hG, hFt, hGt⟩ := derivedStructures (upperStar Λ t)
    (condensedModuleSections Λ T) (condensedModuleSections Λ T₀)
  refine ⟨hF, hG, hFt, hGt, ?_, ?_, ?_, ?_, ?_⟩
  · exact pullback_commShift (upperStar Λ t) _ _ (closedRestrictionSections Λ t)
  · intro K I _ s _ H _ j _
    exact twoResolutionFormula (upperStar Λ t) _ _ (closedRestrictionSections Λ t) K I s H j
  · intro Δ _
    have : NatTrans.CommShift (closedRestrictionRho Λ t) ℤ :=
      pullback_commShift (upperStar Λ t) _ _ (closedRestrictionSections Λ t)
    exact triangleMap _ _ (closedRestrictionRho Λ t) Δ
  · intro J K
    have := moduleProductsExact Λ T J
    have := moduleProductsExact Λ T₀ J
    have := pullback_preservesProducts Λ t J
    have := Functor.preservesLimitsOfShape_discrete_mapDerivedCategory (β := J) (upperStar Λ t)
    have := rightDerived_preservesProducts (J := J) (condensedModuleSections Λ T)
    have := rightDerived_preservesProducts (J := J) (condensedModuleSections Λ T₀)
    have := derived_hasProduct K
    exact productsNaturality _ _ (closedRestrictionRho Λ t) K
  · intro J _ _ D a ha
    refine ⟨filteredModel Λ t D a ha, ?_⟩
    intro P R L M eF eG εF εG α γ hα hγ
    constructor
    · exact continuityRepresentatives D a ha (closedRestrictionPhi Λ T)
        (fun q ↦ condensed_qcqs_globalSections_continuity Λ T D a
          (fun i n hn ↦ by
            have := ha i
            exact (D.obj i).isZero_of_isGE a n hn) q)
        P L eF εF α hα
    · have : PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ t) :=
        (upperStarLowerStarAdjunction Λ t).leftAdjoint_preservesColimits
      apply pullbackContinuityRepresentatives (upperStar Λ t)
        (condensedModuleSections Λ T₀) D a ha ?_ R M eG εG γ hγ
      intro q
      apply condensed_qcqs_globalSections_continuity Λ T₀
        (D ⋙ (upperStar Λ t).mapHomologicalComplex (.up ℤ)) a ?_ q
      intro i n hn
      have := ha i
      exact CochainComplex.isZero_of_isGE
        (((upperStar Λ t).mapHomologicalComplex (.up ℤ)).obj (D.obj i)) a n hn

end AlgebraicGeometry.ProEtale.CondensedRing
