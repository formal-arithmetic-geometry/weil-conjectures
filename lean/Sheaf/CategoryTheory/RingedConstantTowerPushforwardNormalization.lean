/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Category.ULift
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Constant strict towers and ringed direct image

Source: Stacks Project, Cohomology on Sites, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, specialized to constant towers
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization).

The natural number n denotes positive tower level n+1. The comparisons supplied as
parameters below are characterized by their ordinary localization equations; they are
models of the specified derived operations, rather than additional geometric assumptions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.all false
set_option linter.unusedVariables false
universe u v w uA vA wA wTA uB vB wB wTB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Additivity of the exact constant tower functor, obtained from its preserved products.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerAdditive
    (A : Type uA) [Category.{vA} A] [Abelian A] :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Canonical evaluation of an exact constant strict tower, using the ordinary identity.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerEvaluation
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.constCompEvaluationObj (D := A) n) ≪≫
      Functor.mapDerivedCategoryIdIso A

/-- The canonical constant-tower/exact-pullback interchange. Its ordinary components
are identities, as specified by compConstIso.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerPullback
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙
        (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Instance shortcut: the abelian structure of module sheaves on a small ringed site,
the inherited Mathlib `SheafOfModules` instance, recorded once for the statement below.
Source: Stacks Project, Modules on Sites, sheaves of modules; Tag 0A07, constant diagram
specialization (blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerModulesAbelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    Abelian (ringedSiteModules.{u} R) :=
  inferInstance

/-- Instance shortcut: strict inverse sequences of module sheaves form the abelian functor
category, with levelwise kernels and cokernels (Mathlib's `functorCategoryAbelian`).
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerTowersAbelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    Abelian (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) :=
  inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def rct_eval_const_adj
    (A : Type uA) [Category.{vA} A] :
    (evaluation ℕᵒᵖ A).obj (Opposite.op 0) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦
            { app := fun n ↦ X.map (homOfLE (Nat.zero_le n.unop)).op ≫ f
              naturality := by
                intro i j g
                change X.map g ≫
                    (X.map (homOfLE (Nat.zero_le j.unop)).op ≫ f) =
                  (X.map (homOfLE (Nat.zero_le i.unop)).op ≫ f) ≫ 𝟙 Y
                erw [Category.comp_id, ← X.map_comp_assoc]
                congr 2 }
          invFun := fun f ↦ f.app (Opposite.op 0)
          left_inv := by intro f; simp
          right_inv := by
            intro f
            ext n
            simpa using (f.naturality (homOfLE (Nat.zero_le n.unop)).op).symm } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_const_ki
    (A : Type uA) [Category.{vA} A] [Abelian A]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) := by
  have := (rct_eval_const_adj A).preservesKInjectiveComplexes
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_derives
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wB} B]
    (G : A ⥤ B) [G.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    erw [← he]
    exact (G.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_unit_iso
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) [G.Additive] (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) :=
  (rct_derives G).isIso_of_isRightDerivedFunctor η (CochainComplex.KInjectives.mk I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_comparison
    {A : Type uA} {B : Type uB} {Ap : Type u} {Bp : Type v}
    [Category.{vA} A] [Category.{vB} B] [Category Ap] [Category Bp]
    [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} Ap] [HasDerivedCategory.{wTB} Bp]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
    (G : A ⥤ B) (Gp : Ap ⥤ Bp) [G.Additive] [Gp.Additive]
    (r : A ⥤ Ap) (s : B ⥤ Bp) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (h : G ⋙ s ≅ r ⋙ Gp)
    (hr : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj I))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (RGp : DerivedCategory Ap ⥤ DerivedCategory Bp)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (ηp : Gp.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGp)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    [RGp.IsRightDerivedFunctor ηp (HomologicalComplex.quasiIso Ap (.up ℤ))] :
    ∃ χ : RG ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RGp,
      ∀ I : CochainComplex A ℤ,
        s.mapDerivedCategory.map (η.app I) ≫ χ.hom.app (DerivedCategory.Q.obj I) ≫
            RGp.map (r.mapDerivedCategoryFactors.hom.app I) =
          s.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex h (.up ℤ)).hom.app I) ≫
            ηp.app ((r.mapHomologicalComplex (.up ℤ)).obj I) := by
  -- Both comparisons are right-derived units: check this on K-injectives.
  let α := Functor.whiskerRight η s.mapDerivedCategory
  let δ : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ s.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ r.mapDerivedCategory ⋙ RGp :=
    Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ))
        s.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex h (.up ℤ)).hom
        DerivedCategory.Q ≫
      Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) ηp ≫
      Functor.whiskerRight r.mapDerivedCategoryFactors.inv RGp
  have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ s.mapDerivedCategory) := by
    intro X Y f hf
    have hi : IsIso (DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map f.hom)) := rct_derives G f hf
    change IsIso (s.mapDerivedCategory.map (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map f.hom)))
    infer_instance
  have hα : (RG ⋙ s.mapDerivedCategory).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso (L₂ := DerivedCategory.Q)
      (RF := RG ⋙ s.mapDerivedCategory) α
    intro I
    letI : I.obj.IsKInjective := I.property
    have hi : IsIso (η.app I.obj) := rct_unit_iso G RG η I.obj
    change IsIso (s.mapDerivedCategory.map (η.app I.obj))
    infer_instance
  have hδ : (r.mapDerivedCategory ⋙ RGp).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso (L₂ := DerivedCategory.Q)
      (RF := r.mapDerivedCategory ⋙ RGp) δ
    intro I
    letI := hr I.obj I.property
    have := rct_unit_iso Gp RGp ηp ((r.mapHomologicalComplex (.up ℤ)).obj I.obj)
    change IsIso (s.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex h (.up ℤ)).hom.app I.obj) ≫
      ηp.app ((r.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      RGp.map (r.mapDerivedCategoryFactors.inv.app I.obj))
    infer_instance
  -- Uniqueness supplies an isomorphism together with its localization equation.
  let χ := Functor.rightDerivedUnique (RG ⋙ s.mapDerivedCategory)
    (r.mapDerivedCategory ⋙ RGp) α δ (HomologicalComplex.quasiIso A (.up ℤ))
  refine ⟨χ, fun I ↦ ?_⟩
  have hh := Functor.rightDerivedNatTrans_app (RG ⋙ s.mapDerivedCategory)
    (r.mapDerivedCategory ⋙ RGp) α δ (HomologicalComplex.quasiIso A (.up ℤ))
      (𝟙 _) I
  simp only [NatTrans.id_app, Category.id_comp] at hh
  change s.mapDerivedCategory.map (η.app I) ≫ χ.hom.app _ = δ.app I at hh
  rw [← Category.assoc, hh]
  simp [δ, ← RGp.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_complex_refl
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (I : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app I = 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_id_fac
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (I : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj I) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app I := by
  have h := congr_app (congr_arg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh A))
    ((HomotopyCategory.quotient A (.up ℤ)).obj I)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id, Functor.map_id,
    Category.comp_id] at h
  erw [Functor.map_id, Category.comp_id, Category.comp_id] at h
  erw [h, Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [Functor.map_id, Functor.map_id, Category.id_comp,
    Category.comp_id, Category.comp_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_eval_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    (n : ℕᵒᵖ) (I : CochainComplex A ℤ) :
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app I) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) =
      (ringedConstantTowerEvaluation A n).hom.app (DerivedCategory.Q.obj I) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac
    (Functor.const ℕᵒᵖ : A ⥤ _) ((evaluation ℕᵒᵖ A).obj n) I
  simp only [rct_complex_refl, Functor.map_id, Category.comp_id] at hc
  simp only [ringedConstantTowerEvaluation, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, rct_id_fac]
  rw [Functor.mapDerivedCategoryNatIso_fac, ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_pull_fac
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex B ℤ) :
    (ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app I) ≫
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) =
      ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app I) ≫
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app
          (((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).inv.app I) := by
  have hF := Functor.mapDerivedCategoryCompIso_fac
    (Functor.const ℕᵒᵖ : B ⥤ _) ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) I
  have hG := Functor.mapDerivedCategoryCompIso_fac F (Functor.const ℕᵒᵖ : A ⥤ _) I
  simp only [rct_complex_refl] at hF hG
  erw [Functor.map_id, Category.comp_id] at hF hG
  simp only [ringedConstantTowerPullback, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [hG, Functor.mapDerivedCategoryNatIso_fac, ← hF]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_counit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG)
    (hd : ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
      (g : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ η.app I)
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have hh := hd _ I ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hc : (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ := by
    erw [← Adjunction.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  erw [hc, DerivedCategory.Q.map_id, Category.id_comp] at hh
  have hhh := (congrArg (d.homEquiv _ _).symm hh).symm
  dsimp only [Functor.comp_obj] at hhh ⊢
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] using hhh

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [Abelian.HasKInjectiveResolutions A]
    {E : Type uB} [Category.{vB} E] {H₁ H₂ : DerivedCategory A ⥤ E}
    (α β : H₁ ⟶ H₂)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (DerivedCategory.Q.objPreimage X)
  have := hi
  let e : X ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map i)
  apply (cancel_mono (H₂.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h I hI]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_limit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (L : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (ηL : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L)
    [L.IsRightDerivedFunctor ηL (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))] :
    ∃ b : 𝟭 (DerivedCategory A) ≅
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ L,
      ∀ I : CochainComplex A ℤ,
        b.hom.app (DerivedCategory.Q.obj I) ≫
            L.map ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).unit (.up ℤ)).app I) ≫
            ηL.app (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) := by
  let Δ := (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A))
  let u := (constLimAdj : Δ ⊣ lim).unit
  have hu : IsIso u := inferInstance
  let δ : DerivedCategory.Q (C := A) ⟶ DerivedCategory.Q ⋙ Δ.mapDerivedCategory ⋙ L :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex u (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft (Δ.mapHomologicalComplex (.up ℤ)) ηL ≫
      Functor.whiskerRight Δ.mapDerivedCategoryFactors.inv L
  have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (DerivedCategory.Q (C := A)) := by
    intro I J f hf
    have : QuasiIso f.hom := hf
    change IsIso (DerivedCategory.Q.map f.hom)
    infer_instance
  have hδ : (Δ.mapDerivedCategory ⋙ L).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso (L₂ := DerivedCategory.Q)
      (RF := Δ.mapDerivedCategory ⋙ L) δ
    intro I
    letI : I.obj.IsKInjective := I.property
    letI := rct_const_ki A I.obj
    have hη : IsIso (ηL.app ((Δ.mapHomologicalComplex (.up ℤ)).obj I.obj)) :=
      rct_unit_iso lim L ηL ((Δ.mapHomologicalComplex (.up ℤ)).obj I.obj)
    have hmap : IsIso ((NatTrans.mapHomologicalComplex u (.up ℤ)).app I.obj) := by
      change IsIso ((NatIso.mapHomologicalComplex (asIso u) (.up ℤ)).hom.app I.obj)
      infer_instance
    change IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app
      I.obj) ≫ ηL.app ((Δ.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
        L.map (Δ.mapDerivedCategoryFactors.inv.app I.obj))
    infer_instance
  have hid : (𝟭 (DerivedCategory A)).IsRightDerivedFunctor
      (L := DerivedCategory.Q (C := A)) (𝟙 DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts (L := DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (.up ℤ)) _ (Functor.rightUnitor _)
  let b := Functor.rightDerivedUnique (L := DerivedCategory.Q (C := A))
    (𝟭 (DerivedCategory A)) (Δ.mapDerivedCategory ⋙ L)
    (𝟙 DerivedCategory.Q) δ (HomologicalComplex.quasiIso A (.up ℤ))
  refine ⟨b, fun I ↦ ?_⟩
  have hh := Functor.rightDerivedNatTrans_app (L := DerivedCategory.Q (C := A))
    (𝟭 (DerivedCategory A))
    (Δ.mapDerivedCategory ⋙ L) (𝟙 DerivedCategory.Q) δ
    (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 _) I
  simp only [NatTrans.id_app, Category.id_comp] at hh
  change b.hom.app (DerivedCategory.Q.obj I) = δ.app I at hh
  rw [hh]
  change (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app I) ≫
    ηL.app ((Δ.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.map (Δ.mapDerivedCategoryFactors.inv.app I)) ≫
        L.map (Δ.mapDerivedCategoryFactors.hom.app I) = _
  rw [Category.assoc, Category.assoc, ← L.map_comp, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_ordinary_counit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (I : CochainComplex A ℤ) :
    (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G) (.up ℤ)).hom.app I) ≫
      (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).counit.app
        (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)) =
    (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      ((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  ext z : 1
  apply NatTrans.ext
  funext n
  simp only [HomologicalComplex.comp_f, NatTrans.comp_app,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Adjunction.whiskerRight_counit_app_app, Functor.const_obj_map, Functor.compConstIso]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_normalization
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (G : A ⥤ B) [G.Additive]
    (F : B ⥤ A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (RT : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤
      B))
    (LR : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (LS : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (ηT : ((Functor.whiskeringRight ℕᵒᵖ A B).obj
      G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RT)
    (ηR : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LR)
    (ηS : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LS)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    [RT.IsRightDerivedFunctor ηT (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up
      ℤ))]
    [LR.IsRightDerivedFunctor ηR (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up
      ℤ))]
    [LS.IsRightDerivedFunctor ηS (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up
      ℤ))]
    (c : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ G ≅
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj
      G) ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B))
    (hc : ∀ M : (ℕᵒᵖ ⥤ A), c.hom.app M = limit.post M G)
    (a : LR ⋙ RG ≅ RT ⋙ LS)
    (ha : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      η.app ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj X) ≫
          RG.map (ηR.app X) ≫ a.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app X) ≫
          ηS.app (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex
            (.up ℤ) |>.obj X) ≫ LS.map (ηT.app X))
    (β : ∀ n : ℕᵒᵖ, RT ⋙ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ RG)
    (hβ : ∀ (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
      (((evaluation ℕᵒᵖ B).obj) n).mapDerivedCategoryFactors.inv.app
          (((Functor.whiskeringRight ℕᵒᵖ A B).obj
            G).mapHomologicalComplex (.up ℤ) |>.obj I) ≫
        (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory).map (ηT.app I) ≫ (β
          n).hom.app (DerivedCategory.Q.obj I) ≫
        RG.map ((((evaluation ℕᵒᵖ A).obj)
          n).mapDerivedCategoryFactors.hom.app I) =
      η.app ((((evaluation ℕᵒᵖ A).obj) n).mapHomologicalComplex (.up ℤ)
        |>.obj I))
    (d : F.mapDerivedCategory ⊣ RG)
    (dT : ((Functor.whiskeringRight ℕᵒᵖ B A).obj
      F).mapDerivedCategory ⊣ RT)
    (hd : ∀ (M : CochainComplex B ℤ) (I : CochainComplex
      A ℤ)
      (g : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ η.app I)
    (hdT : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (I : CochainComplex (ℕᵒᵖ ⥤
      A) ℤ)
      (g : (((Functor.whiskeringRight ℕᵒᵖ B A).obj
        F).mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      dT.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj
            F).mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map
          (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ ηT.app I) :
    ∃ (χ : RG ⋙ (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ≅ (Functor.const ℕᵒᵖ :
        A ⥤ (ℕᵒᵖ ⥤
      A)).mapDerivedCategory ⋙ RT)
      (bR : 𝟭 (DerivedCategory A) ≅
        (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙ LR)
      (bS : 𝟭 (DerivedCategory B) ≅ (Functor.const ℕᵒᵖ :
        B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⋙ LS),
      (∀ I : CochainComplex A ℤ, I.IsKInjective →
        (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory.map (η.app I)
        ≫ χ.hom.app (DerivedCategory.Q.obj I) ≫
            RT.map ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategoryFactors.hom.app I) =
          (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategoryFactors.hom.app
              (G.mapHomologicalComplex (.up ℤ) |>.obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ G) (.up ℤ)).hom.app I) ≫
            ηT.app ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ (M : DerivedCategory A) (n : ℕᵒᵖ),
        (ringedConstantTowerEvaluation B n).inv.app (RG.obj M) ≫
            (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory).map (χ.hom.app
              M) ≫ (β n).hom.app ((Functor.const ℕᵒᵖ : A ⥤
              (ℕᵒᵖ ⥤ A)).mapDerivedCategory.obj M) ≫
            RG.map ((ringedConstantTowerEvaluation A n).hom.app M) = 𝟙
              (RG.obj M)) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective →
        bR.hom.app (DerivedCategory.Q.obj I) ≫
            LR.map ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤
              A)) ⊣ (lim : (ℕᵒᵖ ⥤ A) ⥤
              A)).unit (.up ℤ)).app I) ≫
            ηR.app ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ I : CochainComplex B ℤ, I.IsKInjective →
        bS.hom.app (DerivedCategory.Q.obj I) ≫
            LS.map ((Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤
              B)) ⊣ (lim : (ℕᵒᵖ ⥤ B) ⥤
              B)).unit (.up ℤ)).app I) ≫
            ηS.app ((Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ M : DerivedCategory A,
        RG.map (bR.hom.app M) ≫ a.hom.app ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤
          A)).mapDerivedCategory.obj M) ≫
            LS.map (χ.inv.app M) ≫ bS.inv.app (RG.obj M) = 𝟙 (RG.obj M)) ∧
      (∀ M : DerivedCategory A,
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj
          F).mapDerivedCategory.map (χ.hom.app M) ≫ dT.counit.app ((Functor.const ℕᵒᵖ :
          A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory.obj M) =
          (ringedConstantTowerPullback F).hom.app (RG.obj M) ≫
            (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory.map (d.counit.app M)) := by
  obtain ⟨χ, hχ⟩ := rct_comparison G
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G)
    (Functor.const ℕᵒᵖ) (Functor.const ℕᵒᵖ)
    (Functor.compConstIso ℕᵒᵖ G)
    (fun I hI ↦ by letI := hI; exact rct_const_ki _ I) RG RT η ηT
  obtain ⟨bR, hbR⟩ := rct_limit LR ηR
  obtain ⟨bS, hbS⟩ := rct_limit LS ηS
  refine ⟨χ, bR, bS, (fun I _ ↦ hχ I), ?_,
    (fun I _ ↦ hbR I), (fun I _ ↦ hbS I), ?_, ?_⟩
  · intro M n
    clear hd hdT ha hc d dT a c
    let ΔR := (Functor.const ℕᵒᵖ : A ⥤ _)
    let ΔS := (Functor.const ℕᵒᵖ : B ⥤ _)
    let eR := (evaluation ℕᵒᵖ A).obj n
    let eS := (evaluation ℕᵒᵖ B).obj n
    let γ : RG ⟶ RG :=
      Functor.whiskerLeft RG (ringedConstantTowerEvaluation _ n).inv ≫
        Functor.whiskerRight χ.hom eS.mapDerivedCategory ≫
        Functor.whiskerLeft ΔR.mapDerivedCategory (β n).hom ≫
        Functor.whiskerRight (ringedConstantTowerEvaluation _ n).hom RG
    suffices hγ : γ = 𝟙 RG from congr_app hγ M
    apply rct_ext
    intro I hI
    letI := hI
    let T := (ΔR.mapHomologicalComplex (.up ℤ)).obj I
    let H := (G.mapHomologicalComplex (.up ℤ)).obj I
    have ht : CochainComplex.IsKInjective T := rct_const_ki _ I
    have hη : IsIso (η.app I) := rct_unit_iso G RG η I
    apply (cancel_epi (η.app I)).mp
    change η.app I ≫
        ((ringedConstantTowerEvaluation _ n).inv.app (RG.obj (DerivedCategory.Q.obj I)) ≫
        eS.mapDerivedCategory.map (χ.hom.app (DerivedCategory.Q.obj I)) ≫
        (β n).hom.app (ΔR.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
        RG.map ((ringedConstantTowerEvaluation _ n).hom.app (DerivedCategory.Q.obj I))) = _
    erw [← Category.assoc,
      (ringedConstantTowerEvaluation B n).inv.naturality]
    erw [← rct_eval_fac _ n I, RG.map_comp]
    simp only [Category.assoc]
    have hbn := (β n).hom.naturality (ΔR.mapDerivedCategoryFactors.hom.app I)
    simp only [Functor.comp_map] at hbn
    erw [← reassoc_of% hbn]
    have hn := congrArg eS.mapDerivedCategory.map (hχ I)
    simp only [Functor.map_comp] at hn
    erw [reassoc_of% hn]
    have he : (ringedConstantTowerEvaluation B n).inv.app
          (DerivedCategory.Q.obj H) ≫
        eS.mapDerivedCategory.map (ΔS.mapDerivedCategoryFactors.hom.app H) =
      eS.mapDerivedCategoryFactors.inv.app ((ΔS.mapHomologicalComplex (.up ℤ)).obj H) := by
      apply (cancel_mono (eS.mapDerivedCategoryFactors.hom.app _)).mp
      erw [Category.assoc, rct_eval_fac, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
      rfl
    erw [reassoc_of% he]
    have hz : eS.mapDerivedCategoryFactors.inv.app
          ((ΔS.mapHomologicalComplex (.up ℤ)).obj H) ≫
        eS.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G)
            (.up ℤ)).hom.app I)) =
      eS.mapDerivedCategoryFactors.inv.app
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
          (.up ℤ)).obj T) := by
      erw [← eS.mapDerivedCategoryFactors.inv.naturality]
      change DerivedCategory.Q.map (𝟙 H) ≫ _ = _
      erw [Functor.map_id, Category.id_comp]
      rfl
    erw [reassoc_of% hz, hβ n T ht]
    change η.app I = η.app I ≫ 𝟙 _
    erw [Category.comp_id]
  · intro M
    clear hd hdT d dT hβ β
    let ΔR := (Functor.const ℕᵒᵖ : A ⥤ _)
    let ΔS := (Functor.const ℕᵒᵖ : B ⥤ _)
    let γ : RG ⟶ ΔR.mapDerivedCategory ⋙ RT ⋙ LS :=
      Functor.whiskerRight bR.hom RG ≫ Functor.whiskerLeft ΔR.mapDerivedCategory a.hom
    let δ : RG ⟶ ΔR.mapDerivedCategory ⋙ RT ⋙ LS :=
      Functor.whiskerLeft RG bS.hom ≫ Functor.whiskerRight χ.hom LS
    have hγδ : γ = δ := by
      apply rct_ext
      intro I hI
      letI := hI
      let H := (G.mapHomologicalComplex (.up ℤ)).obj I
      let T := (ΔR.mapHomologicalComplex (.up ℤ)).obj I
      let uR := (NatTrans.mapHomologicalComplex
        (constLimAdj : ΔR ⊣ lim).unit (.up ℤ)).app I
      let uS := (NatTrans.mapHomologicalComplex
        (constLimAdj : ΔS ⊣ lim).unit (.up ℤ)).app H
      let k := (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G)
        (.up ℤ)).hom.app I
      have hη : IsIso (η.app I) := rct_unit_iso G RG η I
      apply (cancel_epi (η.app I)).mp
      apply (cancel_mono (LS.map (RT.map (ΔR.mapDerivedCategoryFactors.hom.app I)))).mp
      change (η.app I ≫ (RG.map (bR.hom.app _) ≫ a.hom.app _)) ≫ _ =
        (η.app I ≫ (bS.hom.app _ ≫ LS.map (χ.hom.app _))) ≫ _
      simp only [Category.assoc]
      have han := a.hom.naturality (ΔR.mapDerivedCategoryFactors.hom.app I)
      simp only [Functor.comp_map] at han
      erw [← han, ← RG.map_comp_assoc, hbR I, RG.map_comp]
      simp only [Category.assoc]
      erw [← η.naturality_assoc, ha T]
      erw [bS.hom.naturality_assoc, ← LS.map_comp, ← LS.map_comp, hχ I,
        LS.map_comp, LS.map_comp]
      erw [← Category.assoc (bS.hom.app _), hbS H]
      simp only [Category.assoc]
      have hsn := ηS.naturality k
      simp only [Functor.comp_map] at hsn
      erw [← reassoc_of% hsn]
      have ho : (G.mapHomologicalComplex (.up ℤ)).map uR ≫
          (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app T =
        uS ≫ ((lim : (ℕᵒᵖ ⥤ B) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map k := by
        ext z : 1
        apply limit.hom_ext
        intro n
        simp [uR, uS, k, T, H, ΔR, ΔS, NatTrans.mapHomologicalComplex,
          Adjunction.mapHomologicalComplex, constLimAdj, hc, Functor.compConstIso]
      erw [← DerivedCategory.Q.map_comp_assoc, ho, DerivedCategory.Q.map_comp]
      erw [Category.assoc]
      rfl
    have hh := congr_app hγδ M
    change RG.map (bR.hom.app M) ≫ a.hom.app _ = bS.hom.app (RG.obj M) ≫
      LS.map (χ.hom.app M) at hh
    erw [reassoc_of% hh]
    erw [← LS.map_comp_assoc, Iso.hom_inv_id_app]
    erw [LS.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  · intro M
    clear ha hc a c hβ β hbR hbS bR bS
    let ΔR := (Functor.const ℕᵒᵖ : A ⥤ _)
    let ΔS := (Functor.const ℕᵒᵖ : B ⥤ _)
    let FT := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
    let GT := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G
    let γ : RG ⋙ ΔS.mapDerivedCategory ⋙ FT.mapDerivedCategory ⟶ ΔR.mapDerivedCategory :=
      Functor.whiskerRight χ.hom FT.mapDerivedCategory ≫
        Functor.whiskerLeft ΔR.mapDerivedCategory dT.counit
    let δ : RG ⋙ ΔS.mapDerivedCategory ⋙ FT.mapDerivedCategory ⟶ ΔR.mapDerivedCategory :=
      Functor.whiskerLeft RG (ringedConstantTowerPullback F).hom ≫
        Functor.whiskerRight d.counit ΔR.mapDerivedCategory
    suffices hh : γ = δ from congr_app hh M
    apply rct_ext
    intro I hI
    letI := hI
    let H := (G.mapHomologicalComplex (.up ℤ)).obj I
    let T := (ΔR.mapHomologicalComplex (.up ℤ)).obj I
    let k := (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G)
      (.up ℤ)).hom.app I
    have hη : IsIso (η.app I) := rct_unit_iso G RG η I
    apply (cancel_epi (FT.mapDerivedCategory.map (ΔS.mapDerivedCategory.map (η.app I)))).mp
    apply (cancel_mono (ΔR.mapDerivedCategoryFactors.hom.app I)).mp
    change (_ ≫ (FT.mapDerivedCategory.map (χ.hom.app _) ≫ dT.counit.app _)) ≫ _ =
      (_ ≫ ((ringedConstantTowerPullback F).hom.app _ ≫
        ΔR.mapDerivedCategory.map (d.counit.app _))) ≫ _
    simp only [Category.assoc]
    have hdn := dT.counit.naturality (ΔR.mapDerivedCategoryFactors.hom.app I)
    simp only [Functor.id_map, Functor.comp_map] at hdn
    erw [← hdn, ← FT.mapDerivedCategory.map_comp_assoc,
      ← FT.mapDerivedCategory.map_comp_assoc, Category.assoc, hχ I]
    erw [FT.mapDerivedCategory.map_comp, FT.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [rct_counit FT GT (adj.whiskerRight ℕᵒᵖ) RT ηT dT hdT T]
    erw [FT.mapDerivedCategoryFactors.hom.naturality_assoc]
    have hcn := ΔR.mapDerivedCategoryFactors.hom.naturality
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)
    simp only [Functor.comp_map] at hcn
    erw [(ringedConstantTowerPullback F).hom.naturality_assoc,
      ← ΔR.mapDerivedCategory.map_comp_assoc, rct_counit F G adj RG η d hd I,
      ΔR.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [hcn]
    erw [reassoc_of% (rct_pull_fac F H)]
    simp only [Functor.comp_map, Category.assoc, ← DerivedCategory.Q.map_comp]
    apply (cancel_epi (FT.mapDerivedCategory.map
      (ΔS.mapDerivedCategoryFactors.hom.app H))).mpr
    apply (cancel_epi (FT.mapDerivedCategoryFactors.hom.app
      ((ΔS.mapHomologicalComplex (.up ℤ)).obj H))).mpr
    exact congrArg DerivedCategory.Q.map (rct_ordinary_counit F G adj I)

/-- A constant strict tower commutes with total derived direct image, with the specified
representative, evaluation, limit and whole-tower counit normalizations.
Source: Stacks Project, Tag 0A07, lemma-Rf-commutes-with-Rlim, first proof;
Derived Categories, Tags 08BJ, 070K, 070I and 09T5
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization).

Proof plan (the eight steps of the node):
1. Apply small-module-diagrams-grothendieck to the point and the inverse-sequence category.
Functorial K-injective resolutions exist. Levelwise kernels and cokernels make constants,
evaluation and F on towers exact; exact-functor-derived-factorization localizes them.
2. A tower map to a constant tower is determined at terminal index 0. Hence evaluation at
0 is exact left adjoint to constants. Right-adjoint-preserves-kinjective implies that the
constant tower on a K-injective complex is K-injective.
3. The same preservation theorem for adj implies that GJ is K-injective. Both constant
complexes are K-injective, and their ordinary direct-image square is the identity square.
4. Define chi on QJ by the two derived units and this ordinary square. K-injective-total-
derived makes the units invertible. The K-injective Hom bijection and termwise-adjunction-
homotopy descend the construction naturally and independently of representatives.
5. Substitute the unit-normalization equation for beta in the representative equation for
chi. Cancel the invertible unit to obtain the displayed identity at every evaluation.
6. The cone of identity maps computes lim of a constant ordinary tower. Derive its unit
on a K-injective constant tower to obtain bR and bS, then descend by the same Hom bijection.
7. The normalization of a is the derived comparison of the common ordinary composite.
On the constant K-injective model it is the identity of GJ. Insert bR, bS and chi and cancel
to obtain the whole-map limit identity; no faithfulness of evaluated maps is asserted.
8. The Hom normalizations for d and dT compute their counits by ordinary counit chain maps
on J and its constant tower. The ordinary tower counit is the constant ordinary counit.
Localize this chain-map identity and insert the exact interchange to obtain the strict
counit equation in the derived category of towers. Naturality gives every derived object. -/
theorem ringedConstantTowerPushforwardNormalization
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)] [HasDerivedCategory.{w}
      (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} S))]
    (f : RingedToposMorphism R S) [IsIso f.ringMap]
    (F : (ringedSiteModules.{u} S) ⥤ (ringedSiteModules.{u} R)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ f.modules)
    (RG : DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory (ringedSiteModules.{u} S))
    (RT : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ DerivedCategory (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} S)))
    (LR : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ DerivedCategory (ringedSiteModules.{u}
      R))
    (LS : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ DerivedCategory (ringedSiteModules.{u}
      S))
    (η : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (ηT : ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
      f.modules).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RT)
    (ηR : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u}
      R)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LR)
    (ηS : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ (ringedSiteModules.{u}
      S)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LS)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ringedSiteModules.{u} R) (.up ℤ))]
    [RT.IsRightDerivedFunctor ηT (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) (.up
      ℤ))]
    [LR.IsRightDerivedFunctor ηR (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) (.up
      ℤ))]
    [LS.IsRightDerivedFunctor ηS (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) (.up
      ℤ))]
    (c : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u} R)) ⋙ f.modules ≅
      ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
      f.modules) ⋙ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ (ringedSiteModules.{u} S)))
    (hc : ∀ M : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)), c.hom.app M = limit.post M f.modules)
    (a : LR ⋙ RG ≅ RT ⋙ LS)
    (ha : ∀ X : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ℤ,
      η.app ((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u}
        R)).mapHomologicalComplex (.up ℤ) |>.obj X) ≫
          RG.map (ηR.app X) ≫ a.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app X) ≫
          ηS.app (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u}
            S)).obj f.modules).mapHomologicalComplex (.up ℤ) |>.obj X) ≫ LS.map (ηT.app X))
    (β : ∀ n : ℕᵒᵖ, RT ⋙ ((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj n).mapDerivedCategory ⋙ RG)
    (hβ : ∀ (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ℤ), I.IsKInjective →
      (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj) n).mapDerivedCategoryFactors.inv.app
          (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
            f.modules).mapHomologicalComplex (.up ℤ) |>.obj I) ≫
        (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory).map (ηT.app I) ≫ (β
          n).hom.app (DerivedCategory.Q.obj I) ≫
        RG.map ((((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj)
          n).mapDerivedCategoryFactors.hom.app I) =
      η.app ((((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj) n).mapHomologicalComplex (.up ℤ)
        |>.obj I))
    (d : F.mapDerivedCategory ⊣ RG)
    (dT : ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
      F).mapDerivedCategory ⊣ RT)
    (hd : ∀ (M : CochainComplex (ringedSiteModules.{u} S) ℤ) (I : CochainComplex
      (ringedSiteModules.{u} R) ℤ)
      (g : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ η.app I)
    (hdT : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ℤ) (I : CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} R)) ℤ)
      (g : (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
        F).mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      dT.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
            F).mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map
          (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ ηT.app I) :
    ∃ (χ : RG ⋙ (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
      S))).mapDerivedCategory ≅ (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} R))).mapDerivedCategory ⋙ RT)
      (bR : 𝟭 (DerivedCategory (ringedSiteModules.{u} R)) ≅ (Functor.const ℕᵒᵖ :
        (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory ⋙ LR)
      (bS : 𝟭 (DerivedCategory (ringedSiteModules.{u} S)) ≅ (Functor.const ℕᵒᵖ :
        (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S))).mapDerivedCategory ⋙ LS),
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ, I.IsKInjective →
        (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
          S))).mapDerivedCategory.map (η.app I) ≫ χ.hom.app (DerivedCategory.Q.obj I) ≫
            RT.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategoryFactors.hom.app I) =
          (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
            S))).mapDerivedCategoryFactors.hom.app
              (f.modules.mapHomologicalComplex (.up ℤ) |>.obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ f.modules) (.up ℤ)).hom.app I) ≫
            ηT.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ (M : DerivedCategory (ringedSiteModules.{u} R)) (n : ℕᵒᵖ),
        (ringedConstantTowerEvaluation (ringedSiteModules.{u} S) n).inv.app (RG.obj M) ≫
            (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory).map (χ.hom.app
              M) ≫ (β n).hom.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤
              (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) ≫
            RG.map ((ringedConstantTowerEvaluation (ringedSiteModules.{u} R) n).hom.app M) = 𝟙
              (RG.obj M)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ, I.IsKInjective →
        bR.hom.app (DerivedCategory.Q.obj I) ≫
            LR.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
              (ringedSiteModules.{u} R))) ⊣ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤
              (ringedSiteModules.{u} R))).unit (.up ℤ)).app I) ≫
            ηR.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} S) ℤ, I.IsKInjective →
        bS.hom.app (DerivedCategory.Q.obj I) ≫
            LS.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              S))).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤
              (ringedSiteModules.{u} S))) ⊣ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤
              (ringedSiteModules.{u} S))).unit (.up ℤ)).app I) ≫
            ηS.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              S))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u} R),
        RG.map (bR.hom.app M) ≫ a.hom.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
          (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) ≫
            LS.map (χ.inv.app M) ≫ bS.inv.app (RG.obj M) = 𝟙 (RG.obj M)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u} R),
        ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
          F).mapDerivedCategory.map (χ.hom.app M) ≫ dT.counit.app ((Functor.const ℕᵒᵖ :
          (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) =
          (ringedConstantTowerPullback F).hom.app (RG.obj M) ≫
            (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategory.map (d.counit.app M)) := by
  letI : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤ ringedSiteModules.{u} R).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ⥤ ringedSiteModules.{u} S).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI := SheafOfModules.isGrothendieckAbelian R
  letI := SheafOfModules.isGrothendieckAbelian S
  letI := smallModuleDiagrams_isGrothendieckAbelian J R (AsSmall.{u} ℕᵒᵖ)
  letI := smallModuleDiagrams_isGrothendieckAbelian K S (AsSmall.{u} ℕᵒᵖ)
  letI : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) :=
    IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ)).symm
  letI : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) :=
    IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ)).symm
  exact rct_normalization f.modules F adj RG RT LR LS η ηT ηR ηS c hc a ha β hβ d dT hd hdT

end CategoryTheory
