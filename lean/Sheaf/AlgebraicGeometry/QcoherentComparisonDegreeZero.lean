/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
import WeilConjectures.AlgebraicGeometry.AbelianExtSectionsCocycleNormalization
import WeilConjectures.AlgebraicGeometry.TerminalSourceSectionsEvaluation
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Degree-zero normalization of the fixed module and abelian comparison

Source: Stacks Project, Tags 03FD, 015E and 06XR.
-/

@[expose] public section
universe u v u' v' uA
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex HomComplex
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.QcoherentDegreeZeroProof
open ExtEdgeResolution
attribute [local irreducible] Functor.rightDerived


private theorem addEquiv_mk₀
    {A : Type*} [Category A] [Abelian A] [HasExt A]
    {M N : A} (f : M ⟶ N) : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f :=
  Abelian.Ext.addEquiv₀.apply_symm_apply f

private theorem equivHomShift_zero {A : Type*} [Category A] [Preadditive A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ 0 rfl f := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.ofHom, ShiftedHom.mk₀,
    Cochain.rightShift_v, CategoryTheory.shiftFunctorZero',
    CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq]

private theorem extMk_zero
    {A : Type uA} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    {M N : A} (I : InjectiveResolution N) (f : M ⟶ N) :
    I.extMk (f ≫ I.ι.f 0) 1 rfl (by simp) = Abelian.Ext.mk₀ f := by
  let := HasDerivedCategory.standard A
  have hz : Cocycle.fromSingleMk
      ((f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv)
        (zero_add 0) 1 rfl (by simp [I.cochainComplex_d]) =
      Cocycle.ofHom ((CochainComplex.singleFunctor A 0).map f ≫ I.ι') := by
    ext : 1
    apply (Cochain.fromSingleEquiv (zero_add 0)).injective
    simp [Cocycle.fromSingleMk_coe, Cocycle.ofHom, Cochain.fromSingleEquiv,
      Cochain.ofHom_v, I.ι'_f_zero, CochainComplex.singleFunctor, singleFunctors,
      HomologicalComplex.single_map_f_self]
  ext
  erw [I.extMk_hom, hz, equivHomShift_zero, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.mk₀_comp_mk₀, Functor.map_comp,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [Abelian.Ext.mk₀_hom]
  congr 1

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem site_sections_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u})
    (f : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    (siteSectionsObjIso J U F 0).hom (Abelian.Ext.mk₀ f) =
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero.app F
          (sectionsEquiv J U F f) := by
  let I := injectiveResolution F
  let G := sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let s := sectionsEquiv J U F f
  let c := (I.toRightDerivedZero' G) s
  have hc : ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles 0 c =
      (sectionsIso J U).hom.app (I.cocomplex.X 0) (f ≫ I.ι.f 0) := by
    have h := ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles G) s
    change _ = G.map (I.ι.f 0) s at h
    simp only [ConcreteCategory.comp_apply] at h
    apply h.trans
    dsimp only [G, Functor.comp_map, s, sectionsIso, NatIso.ofComponents_hom_app,
      AddEquiv.toAddCommGrpIso_hom]
    exact (sectionsEquiv_naturality J U (I.ι.f 0) f).symm
  have h := canonical_site_sections_cocycle J U F I 0
    (f ≫ I.ι.f 0) (by
      erw [Category.assoc, I.ι_f_zero_comp_complex_d, comp_zero]) c hc
  rw [extMk_zero] at h
  have hr : G.toRightDerivedZero.app F ≫ (I.isoRightDerivedObj G 0).hom =
      I.toRightDerivedZero' G ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0) := by
    rw [I.toRightDerivedZero_eq G]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  apply (ConcreteCategory.bijective_of_isIso (I.isoRightDerivedObj G 0).hom).injective
  exact h.trans (ConcreteCategory.congr_hom hr s).symm

private theorem forget_zero
    {A B D : Type*} [Category A] [Abelian A] [HasInjectiveResolutions A]
    [Category B] [Abelian B] [Category D] [Abelian D]
    (G : A ⥤ B) (V : B ⥤ D) [G.Additive] [V.Additive] [V.PreservesHomology]
    {M : A} (I : InjectiveResolution M) :
    V.map (G.toRightDerivedZero.app M) ≫ (resolutionForgetObjIso G V I 0).hom =
      I.toRightDerivedZero' (G ⋙ V) ≫
        (((G ⋙ V).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 := by
  let L := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let K := (V.mapHomologicalComplex (.up ℕ)).obj L
  let e := (L.sc 0).mapCyclesIso V
  have he : e.inv ≫ K.iCycles 0 = V.map (L.iCycles 0) := by
    apply (cancel_epi e.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact ((L.sc 0).mapCyclesIso_hom_iCycles V).symm
  have hc : V.map (I.toRightDerivedZero' G) ≫ e.inv =
      I.toRightDerivedZero' (G ⋙ V) := by
    apply (cancel_mono (K.iCycles 0)).mp
    rw [Category.assoc, he, ← V.map_comp, I.toRightDerivedZero'_comp_iCycles]
    exact (I.toRightDerivedZero'_comp_iCycles (G ⋙ V)).symm
  have hp : V.map (L.homologyπ 0) ≫ ((L.sc 0).mapHomologyIso V).inv =
      e.inv ≫ K.homologyπ 0 := by
    let h := (L.sc 0).homologyData.left
    dsimp only [e]
    rw [h.mapHomologyIso_eq V, h.mapCyclesIso_eq V]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
    erw [← Category.assoc, ← V.map_comp, h.homologyπ_comp_homologyIso_hom, V.map_comp,
      Category.assoc, (h.map V).π_comp_homologyIso_inv]
    rfl
  rw [I.toRightDerivedZero_eq G]
  dsimp only [resolutionForgetObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [← Category.assoc, ← V.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, V.map_comp]
  change V.map (I.toRightDerivedZero' G) ≫
    V.map (L.homologyπ 0) ≫ ((L.sc 0).mapHomologyIso V).inv = _
  rw [hp, ← Category.assoc, hc]
  rfl

private theorem resolution_zero
    {A B : Type*} [Category A] [Abelian A] [HasInjectiveResolutions A]
    [Category B] [Abelian B] (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    {M : A} {K : CochainComplex A ℕ}
    (ι : (CochainComplex.single₀ A).obj M ⟶ K) [QuasiIso ι]
    (hK : ∀ n, G.rightAcyclic (K.X n))
    (c : G.obj M ⟶ ((G.mapHomologicalComplex (.up ℕ)).obj K).cycles 0)
    (hc : c ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).iCycles 0 = G.map (ι.f 0)) :
    G.toRightDerivedZero.app M ≫ (G.rightDerivedObjIsoOfResolution ι hK 0).hom =
      c ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).homologyπ 0 := by
  let I := injectiveResolution M
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 M) I ι
  let ψ := (G.mapHomologicalComplex (.up ℕ)).map φ
  have hw : ι.f 0 ≫ φ.f 0 = I.ι.f 0 := by
    have h := InjectiveResolution.comp_descOfQuasiIsoFZero (𝟙 M) I ι
    simpa only [Category.id_comp, φ, InjectiveResolution.descOfQuasiIso,
      CochainComplex.mkHom_f_0] using h
  have : QuasiIso ψ :=
    G.quasiIso_map_of_rightAcyclic_nat φ hK
      (fun n ↦ Functor.rightAcyclic_of_injective (I.cocomplex.X n))
  have hm : IsIso (HomologicalComplex.homologyMap ψ 0) := inferInstance
  have he : (G.rightDerivedObjIsoOfResolution ι hK 0).hom ≫
      HomologicalComplex.homologyMap ψ 0 = (I.isoRightDerivedObj G 0).hom := by
    unfold Functor.rightDerivedObjIsoOfResolution InjectiveResolution.isoRightDerivedObjOfQuasiIso
    dsimp only [Iso.trans_hom, Iso.symm_hom, asIso_inv]
    change (_ ≫ inv (HomologicalComplex.homologyMap ψ 0)) ≫
      HomologicalComplex.homologyMap ψ 0 = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hz : c ≫ HomologicalComplex.cyclesMap ψ 0 = I.toRightDerivedZero' G := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hc,
      I.toRightDerivedZero'_comp_iCycles]
    change G.map (ι.f 0) ≫ G.map (φ.f 0) = G.map (I.ι.f 0)
    rw [← G.map_comp, hw]
  apply (cancel_mono (HomologicalComplex.homologyMap ψ 0)).mp
  rw [Category.assoc, he, I.toRightDerivedZero_eq G]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hz]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem terminal_sections_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (T : C) (hT : IsTerminal T)
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (he : ∀ (F : Sheaf J AddCommGrpCat.{u})
      (f : (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F),
      sectionsEquiv J T F (e.hom ≫ f) =
        AddCommGrpCat.uliftZMultiplesAddEquiv _
          ((constantSheafAdj J AddCommGrpCat.{u} hT).homAddEquiv _ F f))
    (F : Sheaf J AddCommGrpCat.{u}) (x : Sheaf.H.{u} F 0) :
    (siteSectionsObjIso J T F 0).hom
      ((Abelian.Ext.mk₀ e.hom).comp x (zero_add 0)) =
    (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)).toRightDerivedZero.app F
        (Sheaf.H.equiv₀.{u, u, u, u} F hT x) := by
  have hx : Abelian.Ext.mk₀ (e.hom ≫ Abelian.Ext.addEquiv₀ x) =
      (Abelian.Ext.mk₀ e.hom).comp x (zero_add 0) := by
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply]
  have h := site_sections_zero J T F
    (e.hom ≫ Abelian.Ext.addEquiv₀ x)
  rw [hx] at h
  have hs : sectionsEquiv J T F
      (e.hom ≫ Abelian.Ext.addEquiv₀ x) =
      Sheaf.H.equiv₀.{u, u, u, u} F hT x := by
    simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
    exact he F (Abelian.Ext.addEquiv₀ x)
  exact h.trans (congrArg
    ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)).toRightDerivedZero.app F)
    hs)

private theorem resolutionSectionsObj_zero
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    [Abelian E] [HasInjectiveResolutions E]
    (S : A ⥤ B) (V : B ⥤ D) (T : A ⥤ E) (Γ : E ⥤ D)
    [S.Additive] [V.Additive] [V.PreservesHomology]
    [T.Additive] [T.PreservesHomology] [Γ.Additive] [PreservesFiniteLimits Γ]
    (σ : S ⋙ V ≅ T ⋙ Γ)
    (κ : S.mapHomologicalComplex (.up ℕ) ⋙ V.mapHomologicalComplex (.up ℕ) ≅
      T.mapHomologicalComplex (.up ℕ) ⋙ Γ.mapHomologicalComplex (.up ℕ))
    (hκ : ∀ (K : CochainComplex A ℕ) (n : ℕ),
      (κ.hom.app K).f n = σ.hom.app (K.X n))
    (s : (S.mapHomologicalComplex (.up ℕ) ⋙ V.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) 0) ≅
      (T.mapHomologicalComplex (.up ℕ) ⋙ Γ.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) 0))
    (hs : ∀ K, s.hom.app K = HomologicalComplex.homologyMap (κ.hom.app K) 0)
    {M : A} (I : InjectiveResolution M)
    (hI : ∀ n, Γ.rightAcyclic (T.obj (I.cocomplex.X n))) :
    V.map (S.toRightDerivedZero.app M) ≫
        (resolutionSectionsObjIso S V T Γ 0 s I hI).hom =
      σ.hom.app M ≫ Γ.toRightDerivedZero.app (T.obj M) := by
  let K := (V.mapHomologicalComplex (.up ℕ)).obj
    ((S.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let K' := (Γ.mapHomologicalComplex (.up ℕ)).obj
    ((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app M ≫
    (T.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    exact quasiIso_comp _ _
  let c := σ.inv.app M ≫ I.toRightDerivedZero' (S ⋙ V) ≫
    HomologicalComplex.cyclesMap (κ.hom.app I.cocomplex) 0
  have hc : c ≫ K'.iCycles 0 = Γ.map (ι.f 0) := by
    dsimp only [c, K']
    simp only [Category.assoc]
    erw [HomologicalComplex.cyclesMap_i]
    erw [← Category.assoc (I.toRightDerivedZero' (S ⋙ V)) _ _,
      I.toRightDerivedZero'_comp_iCycles]
    erw [hκ, σ.hom.naturality]
    erw [← Category.assoc, σ.inv_hom_id_app, Category.id_comp]
    dsimp only [ι, Functor.comp_map, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    change Γ.map (T.map (I.ι.f 0)) =
      Γ.map ((𝟙 (T.obj M) ≫ T.map (𝟙 M)) ≫ T.map (I.ι.f 0))
    erw [T.map_id, Category.id_comp, Category.id_comp]
  have hr := resolution_zero Γ ι hI c hc
  change V.map (S.toRightDerivedZero.app M) ≫
    ((resolutionForgetObjIso S V I 0).hom ≫ s.hom.app I.cocomplex ≫
      (Γ.rightDerivedObjIsoOfResolution ι hI 0).inv) = _
  apply (cancel_mono (Γ.rightDerivedObjIsoOfResolution ι hI 0).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (I.toRightDerivedZero' (S ⋙ V) ≫ K.homologyπ 0) ≫
        s.hom.app I.cocomplex := by
      rw [← Category.assoc, forget_zero S V I]
      rfl
    _ = I.toRightDerivedZero' (S ⋙ V) ≫
        HomologicalComplex.cyclesMap (κ.hom.app I.cocomplex) 0 ≫ K'.homologyπ 0 := by
      dsimp only [K, K']
      erw [Category.assoc, hs, HomologicalComplex.homologyπ_naturality]
      rfl
    _ = σ.hom.app M ≫ (c ≫ K'.homologyπ 0) := by
      dsimp only [c]
      simp only [← Category.assoc, σ.hom_inv_id_app, Category.id_comp]
    _ = _ := congrArg (fun f ↦ σ.hom.app M ≫ f) hr.symm

private theorem resolutionSectionsNat_zero
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    [Abelian E] [HasInjectiveResolutions E]
    (S : A ⥤ B) (V : B ⥤ D) (T : A ⥤ E) (Γ : E ⥤ D)
    [S.Additive] [V.Additive] [V.PreservesHomology]
    [T.Additive] [T.PreservesHomology] [Γ.Additive] [PreservesFiniteLimits Γ]
    (σ : S ⋙ V ≅ T ⋙ Γ)
    (κ : S.mapHomologicalComplex (.up ℕ) ⋙ V.mapHomologicalComplex (.up ℕ) ≅
      T.mapHomologicalComplex (.up ℕ) ⋙ Γ.mapHomologicalComplex (.up ℕ))
    (hκ : ∀ (K : CochainComplex A ℕ) (n : ℕ),
      (κ.hom.app K).f n = σ.hom.app (K.X n))
    (s : (S.mapHomologicalComplex (.up ℕ) ⋙ V.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) 0) ≅
      (T.mapHomologicalComplex (.up ℕ) ⋙ Γ.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) 0))
    (hs : ∀ K, s.hom.app K = HomologicalComplex.homologyMap (κ.hom.app K) 0)
    (hI : ∀ (M : A) [Injective M], Γ.rightAcyclic (T.obj M)) (M : A) :
    V.map (S.toRightDerivedZero.app M) ≫
        ((resolutionSectionsNatIso S V T Γ 0 s hI).app M).hom =
      σ.hom.app M ≫ Γ.toRightDerivedZero.app (T.obj M) := by
  exact resolutionSectionsObj_zero S V T Γ σ κ hκ s hs (injectiveResolution M)
    (fun n ↦ hI _)

private theorem forget_comp_apply
    {R : Type u} [Ring R] {M N : ModuleCat.{u} R} {D : AddCommGrpCat.{u}}
    (f : M ⟶ N) (g : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj N ⟶ D)
    (x : M) : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f ≫ g) x =
      g (f.hom x) := rfl

private theorem native_sections_unit (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
    let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let V := forget₂ (ModuleCat.{u}
      ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
    V.map (G.toRightDerivedZero.app F) ≫
      ((resolutionSectionsNatIso G V T Γ 0 (sectionHomologyIso X 0)
        (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom =
      Γ.toRightDerivedZero.app (T.obj F) := by
  dsimp only
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  have h := resolutionSectionsNat_zero G V T Γ (Iso.refl _) (Iso.refl _)
    (by intro K n; rfl) (sectionHomologyIso X 0) (by
      intro K
      change 𝟙 _ = HomologicalComplex.homologyMap (𝟙 _) 0
      rw [HomologicalComplex.homologyMap_id])
    (fun M _ ↦ forgottenInjectiveAcyclic X M) F
  simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using h

attribute [local irreducible] ExtEdgeResolution.siteSectionsObjIso
  ExtEdgeResolution.siteSectionsNatIso

private theorem site_composite_apply
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (N : Sheaf J AddCommGrpCat.{u})
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (q : ℕ)
    (b : Sheaf.cohomologyPresheafFunctor J q ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q)
    (x : ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj N) :
    ((b.symm ≪≫ siteExtNatIso J U q ≪≫
      extSourceNatIso e q ≪≫ siteHNatIso J q).app N).hom x =
      (Abelian.Ext.precompAddEquiv.{u} e N q).symm ((b.app N).inv x) := by
  change @Eq (Abelian.Ext.{u}
    ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) N q) _ _
  dsimp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom,
    siteExtNatIso, siteHNatIso, Iso.refl_hom, NatTrans.id_app,
    extSourceNatIso, NatIso.ofComponents_hom_app]
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem iso_precomp_zero
    {S N : Type u} {B D : AddCommGrpCat.{u}}
    (d : B ≅ D) (e : N ≃ S) (c : N ≃ B) (b : S → D)
    (he : ∀ y, d.hom (c y) = b (e y)) (s : S) :
    e (c.symm (d.inv (b s))) = s := by
  have h := he (e.symm s)
  rw [e.apply_symm_apply] at h
  have h' : c (e.symm s) = d.inv (b s) :=
    ((ConcreteCategory.bijective_of_isIso d.hom).injective
      (h.trans (Iso.inv_hom_id_apply d (b s)).symm))
  rw [← h', c.symm_apply_apply, e.apply_symm_apply]

private theorem inverse_apply_congr
    {A B : AddCommGrpCat.{u}} (e f : A ≅ B) (h : e = f) (x : B) :
    e.inv x = f.inv x := congrArg (fun z : A ≅ B ↦ z.inv x) h

private theorem site_component_eq
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (N : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
    (siteSectionsNatIso J U q).app N = siteSectionsObjIso J U N q := by
  unfold siteSectionsObjIso
  rfl

private theorem site_component_inv_apply
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (N : Sheaf J AddCommGrpCat.{u}) (q : ℕ)
    (x : ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj N) :
    ((siteSectionsNatIso J U q).app N).inv x = (siteSectionsObjIso J U N q).inv x :=
  inverse_apply_congr _ _ (site_component_eq J U N q) x

private theorem site_composite_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (hU : IsTerminal U) (N : Sheaf J AddCommGrpCat.{u})
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (he : ∀ (M : Sheaf J AddCommGrpCat.{u})
      (f : (constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ M),
      sectionsEquiv J U M (e.hom ≫ f) =
        AddCommGrpCat.uliftZMultiplesAddEquiv _
          ((constantSheafAdj J AddCommGrpCat.{u} hU).homAddEquiv _ M f))
    (s : N.obj.obj (op U)) :
    Sheaf.H.equiv₀.{u, u, u, u} N hU
      ((((siteSectionsNatIso J U 0).symm ≪≫ siteExtNatIso J U 0 ≪≫
        extSourceNatIso e 0 ≪≫ siteHNatIso J 0).app N).hom
          (((Functor.toRightDerivedZero (sheafToPresheaf J AddCommGrpCat.{u} ⋙
            (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).app N) s)) = s := by
  let Γ := sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let c := Abelian.Ext.precompAddEquiv.{u} e N 0
  have h₁ := site_composite_apply J U N e 0 (siteSectionsNatIso J U 0)
    (Γ.toRightDerivedZero.app N s)
  have h₂ := site_component_inv_apply J U N 0 (Γ.toRightDerivedZero.app N s)
  have h₃ := iso_precomp_zero (siteSectionsObjIso J U N 0)
    (Sheaf.H.equiv₀.{u, u, u, u} N hU).toEquiv c.toEquiv
    (fun t ↦ Γ.toRightDerivedZero.app N t)
    (fun y ↦ terminal_sections_zero J U hU e he N y) s
  exact (congrArg (Sheaf.H.equiv₀.{u, u, u, u} N hU)
    (h₁.trans (congrArg c.symm h₂))).trans h₃


private theorem composite_unit_square
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B) (b : B ≅ Q)
    (F : A) {M : ModuleCat.{u} R} (f : M ⟶ K.obj F)
    (g : (forget₂ _ AddCommGrpCat.{u}).obj M ⟶ B.obj (T.obj F))
    (h : (forget₂ _ AddCommGrpCat.{u}).map f ≫ (a.app F).hom = g) :
    (forget₂ _ AddCommGrpCat.{u}).map f ≫
        ((a ≪≫ Functor.isoWhiskerLeft T b).app F).hom =
      g ≫ (b.app (T.obj F)).hom := by
  change _ ≫ ((a.app F).hom ≫ (b.app (T.obj F)).hom) = _
  rw [← Category.assoc, h]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem native_composite_unit (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F) ≫
        ((moduleCohomologyExtResolutionNatIso X 0).app F).hom =
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).toRightDerivedZero.app
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) ≫
      (((siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ 0).symm ≪≫
        siteExtNatIso (Opens.grothendieckTopology X) ⊤ 0 ≪≫
        extSourceNatIso (terminalSourceIso X) 0 ≪≫
        siteHNatIso (Opens.grothendieckTopology X) 0).app
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)).hom := by
  unfold moduleCohomologyExtResolutionNatIso
  refine composite_unit_square _ _ F _ _ ?_
  exact native_sections_unit X F

private theorem evaluate_unit_square
    {R : Type u} [Ring R] {M N : ModuleCat.{u} R} {P Q : AddCommGrpCat.{u}}
    (f : M ⟶ N) (g : (forget₂ _ AddCommGrpCat.{u}).obj N ⟶ P)
    (h : (forget₂ _ AddCommGrpCat.{u}).obj M ⟶ Q) (k : Q ⟶ P)
    (he : (forget₂ _ AddCommGrpCat.{u}).map f ≫ g = h ≫ k)
    (e : P → M) (hz : ∀ x, e (k (h x)) = x) (x : M) :
    e (g (f.hom x)) = x := by
  have hh : g (f.hom x) = k (h x) :=
    (forget_comp_apply f g x).symm.trans (ConcreteCategory.congr_hom he x)
  exact (congrArg e hh).trans (hz x)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem module_sections_zero (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (s : Γ(F, ⊤)) :
    Sheaf.H.equiv₀.{u, u, u, u}
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) isTerminalTop
      (((moduleCohomologyExtResolutionNatIso X 0).app F).hom
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F).hom s)) =
      s := by
  refine evaluate_unit_square
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F)
    ((moduleCohomologyExtResolutionNatIso X 0).app F).hom _ _
    (native_composite_unit X F) _ ?_ s
  intro t
  exact site_composite_zero (Opens.grothendieckTopology X) ⊤ isTerminalTop
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)
    (terminalSourceIso X) (fun N f ↦ terminal_source_sections_evaluation X N f) t

private theorem universe_mk₀
    {A : Type*} [Category A] [Abelian A] [HasExt.{u} A] [HasExt.{u + 1} A]
    {M N : A} (f : M ⟶ N) :
    @coherentExtUniverseEquiv A _ _ ‹HasExt.{u} A› ‹HasExt.{u + 1} A› M N 0
      (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ f := by
  let := HasDerivedCategory.standard A
  apply Abelian.Ext.homAddEquiv.injective
  rw [coherentExtUniverseEquiv_hom]
  simp only [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.mk₀_hom]

private theorem universe_addEquiv₀
    {A : Type*} [Category A] [Abelian A] [hs : HasExt.{u} A] [hl : HasExt.{u + 1} A]
    {M N : A} (x : Abelian.Ext.{u} M N 0) :
    Abelian.Ext.addEquiv₀ (@coherentExtUniverseEquiv A _ _ hs hl M N 0 x) =
      Abelian.Ext.addEquiv₀ x := by
  have h := @universe_mk₀ A _ _ hs hl M N (Abelian.Ext.addEquiv₀ x)
  rw [Abelian.Ext.mk₀_addEquiv₀_apply] at h
  exact (congrArg (@Abelian.Ext.addEquiv₀ _ _ _ hl M N) h).trans
    (addEquiv_mk₀ _)

private theorem universe_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [hs : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hl : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{u})
    (x : @Sheaf.H _ _ J F inferInstance hs 0) :
    @Sheaf.H.equiv₀.{u + 1, u, u, u} _ _ J inferInstance hl F _ hT
      (@coherentExtUniverseEquiv _ _ _ hs hl _ _ 0 x) =
    @Sheaf.H.equiv₀.{u, u, u, u} _ _ J inferInstance hs F _ hT x := by
  unfold Sheaf.H.equiv₀
  exact congrArg
    (fun f ↦ AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj J AddCommGrpCat.{u} hT).homAddEquiv _ F f))
    (@universe_addEquiv₀ _ _ _ hs hl _ F x)

end AlgebraicGeometry.Scheme.Modules.QcoherentDegreeZeroProof

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] moduleAbelianCohomologyLarge coherentExtUniverseEquiv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed common-resolution comparison sends the degree-zero derived image
of a section to that section under terminal evaluation.

Source: Stacks Project, Tags 03FD, 015E and 06XR.
(blueprint: lem-weil-pbc-qcoherent-comparison-degree-zero)

Proof: On an injective resolution, the degree-zero derived unit is the
augmentation followed by the cycle-to-homology map. Exact forgetting preserves
this map. The forgotten resolution is section-acyclic, and the canonical acyclic
resolution comparison preserves its augmentation, so its degree-zero component
has the same formula. The fixed Ext comparison sends the cocycle of a morphism
to its homology class. At the terminal open, the free representable generator
maps to 1 in the constant integer sheaf; consequently the source-change map is
the terminal section evaluation. These identities give the degree-zero formula
for the fixed module comparison. Finally change the Ext presentation universe:
both presentations send a degree-zero morphism to the same derived morphism,
so terminal evaluation is preserved. This includes the empty scheme and zero
modules and needs no quasi-coherence assumption. -/
theorem moduleAbelianCohomologyLarge_zero (X : Scheme.{u})
    (F : X.Modules) (s : Γ(F, ⊤)) :
    letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    CoherentEtale.sourceZero X F
      (moduleAbelianCohomologyLarge X F 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s)) =
      s := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    comparisonHasExt X
  exact (congrArg (CoherentEtale.sourceZero X F)
    (moduleAbelianCohomologyLarge_component X F 0 _)).trans
      ((@QcoherentDegreeZeroProof.universe_zero _ _ (Opens.grothendieckTopology X)
        inferInstance (comparisonHasExt X) (HasExt.standard _) _ isTerminalTop _ _).trans
          (QcoherentDegreeZeroProof.module_sections_zero X F s))

end AlgebraicGeometry.Scheme.Modules
