/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData
import all Sheaf.AlgebraicGeometry.ScalarExtCupDegreeZero

import Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import Sheaf.AlgebraicGeometry.ScalarCohomologyExtZeroGlobalSections
import all Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality
import Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient
import all Sheaf.Paper.ModuleCupCoefficientResolutionMaps
import Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility

/-! # Scalar cup on resolution classes

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private abbrev ResolutionCycles {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :=
  ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K

private theorem class_zero_injective {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) : Function.Injective (D.class 0) := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let K := (S.mapHomologicalComplex (.up ℕ)).obj D.K
  let φ := (S.mapHomologicalComplex (.up ℕ)).map D.comparison
  have : IsIso (HomologicalComplex.homologyMap φ 0) := D.computes 0
  intro a b hab
  apply (ModuleCat.mono_iff_injective ((K.sc 0).moduleCatCyclesIso.inv)).mp inferInstance
  apply (ModuleCat.mono_iff_injective (K.homologyπ 0)).mp inferInstance
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap φ 0)).mp inferInstance
  apply (ModuleCat.mono_iff_injective (D.I.isoRightDerivedObj S 0).inv).mp inferInstance
  exact hab

private def augmentationCycle {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (x : Γ(F, ⊤)) : ResolutionCycles D 0 := by
  refine ⟨(D.augmentation.f 0).val.app (op ⊤) x, ?_⟩
  have h : D.augmentation.f 0 ≫ D.K.d 0 1 = 0 := by
    rw [D.augmentation.comm]
    simp
  change (D.K.d 0 ((ComplexShape.up ℕ).next 0)).val.app (op ⊤)
    ((D.augmentation.f 0).val.app (op ⊤) x) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ)
    (by simp : (ComplexShape.up ℕ).Rel 0 1)]
  exact congrArg (fun t ↦ t.val.app (op ⊤) x) h

private theorem augmentationCycle_class {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {F : X.Modules}
    (D : CupAcyclicResolution F) (x : Γ(F, ⊤)) :
    D.class 0 (augmentationCycle D x) = (scalarGlobalSectionsEquiv f F).symm x := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))
  let K := (S.mapHomologicalComplex (.up ℕ)).obj D.K
  let L := RingedSpace.globalSectionsComplex D.I
  let φ := (S.mapHomologicalComplex (.up ℕ)).map D.comparison
  let a : K.cycles 0 := (K.sc 0).moduleCatCyclesIso.inv (augmentationCycle D x)
  have ha : K.iCycles 0 a = (D.augmentation.f 0).val.app (op ⊤) x := by
    exact ConcreteCategory.congr_hom
      (ShortComplex.moduleCatCyclesIso_inv_iCycles (K.sc 0)) (augmentationCycle D x)
  have hcycles : HomologicalComplex.cyclesMap φ 0 a = (D.I.toRightDerivedZero' S) x := by
    apply (ModuleCat.mono_iff_injective (L.iCycles 0)).mp inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ 0) a
    have hi := ConcreteCategory.congr_hom (D.I.toRightDerivedZero'_comp_iCycles S) x
    simp only [ConcreteCategory.comp_apply] at h hi
    change L.iCycles 0 (HomologicalComplex.cyclesMap φ 0 a) = φ.f 0 (K.iCycles 0 a) at h
    change L.iCycles 0 ((D.I.toRightDerivedZero' S) x) = (D.I.ι.f 0).val.app (op ⊤) x at hi
    exact h.trans ((congrArg (fun t ↦ φ.f 0 t) ha).trans
      ((congrArg (fun t ↦ t.val.app (op ⊤) x)
        (congrArg (fun t ↦ t.f 0) D.over)).trans hi.symm))
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ 0) a
  simp only [ConcreteCategory.comp_apply] at hπ
  change (D.I.isoRightDerivedObj S 0).inv
    (HomologicalComplex.homologyMap φ 0 (K.homologyπ 0 a)) = _
  rw [hπ, hcycles]
  have h := ConcreteCategory.congr_hom (D.I.toRightDerivedZero_eq S) x
  simp only [ConcreteCategory.comp_apply] at h
  change (D.I.isoRightDerivedObj S 0).inv
    (L.homologyπ 0 ((D.I.toRightDerivedZero' S) x)) = _
  exact h.symm
private theorem augmentationCycle_eq {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {F : X.Modules}
    (D : CupAcyclicResolution F) (a : ResolutionCycles D 0) :
    augmentationCycle D (scalarGlobalSectionsEquiv f F (D.class 0 a)) = a := by
  apply class_zero_injective D
  exact (augmentationCycle_class f D _).trans
    ((scalarGlobalSectionsEquiv f F).symm_apply_apply (D.class 0 a))

private theorem scalarExtCup_right_mk₀
    {k : Type w} [Field k] {X : Scheme.{w}} {A B : KSheaf X k} {n : ℕ}
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B n)
    (v : 𝟙_ (KSheaf X k) ⟶ A) :
    scalarExtCup a (Abelian.Ext.mk₀ v) =
      a.comp (Abelian.Ext.mk₀ ((ρ_ B).inv ≫ (B ◁ v))) rfl := by
  have : EnoughInjectives (KSheaf X k) := inferInstance
  unfold scalarExtCup
  rw [Abelian.Ext.mapExactFunctor_mk₀]
  rw [ext_iso_transport (tensorRight (𝟙_ (KSheaf X k)))
    (rightUnitorNatIso (KSheaf X k)) a]
  simp only [rightUnitorNatIso, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, curriedTensor_obj_map]
  simp only [← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀]
  have hunit : (λ_ (𝟙_ (KSheaf X k))).inv ≫
      (ρ_ (𝟙_ (KSheaf X k))).hom = 𝟙 _ := by
    rw [← unitors_equal]
    simp
  rw [hunit, Abelian.Ext.mk₀_id_comp]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
private def rightZeroComponent {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (y : Γ(G, ⊤)) (n : ℕ) :
    D.left.K.X n ⟶ D.target.K.X n where
  val := {
    app := fun V ↦ ModuleCat.ofHom
      ((D.pair n 0 V.unop).flip ((D.right.augmentation.f 0).val.app V
        (G.presheaf.map (homOfLE le_top).op y)))
    naturality := by
      intro V W u
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change D.pair n 0 W.unop ((D.left.K.X n).val.map u a)
        ((D.right.augmentation.f 0).val.app W (G.presheaf.map (homOfLE le_top).op y)) =
          (D.target.K.X n).val.map u (D.pair n 0 V.unop a
            ((D.right.augmentation.f 0).val.app V (G.presheaf.map (homOfLE le_top).op y)))
      have hrest := D.restriction n 0 V.unop W.unop (leOfHom u.unop) a
        ((D.right.augmentation.f 0).val.app V (G.presheaf.map (homOfLE le_top).op y))
      refine Eq.trans ?_ hrest.symm
      apply congrArg (fun t ↦ D.pair n 0 W.unop ((D.left.K.X n).val.map u a) t)
      have haug := Hom.app_presheaf_map (D.right.augmentation.f 0) u.unop
        (G.presheaf.map (homOfLE le_top).op y)
      have hpres : G.presheaf.map u (G.presheaf.map (homOfLE le_top).op y) =
          G.presheaf.map (homOfLE le_top).op y :=
        (presheaf_map_map_apply (M := G) (homOfLE le_top) u.unop y).trans rfl
      exact (congrArg ((D.right.augmentation.f 0).val.app W) hpres.symm).trans haug }

private def rightZeroMap {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (y : Γ(G, ⊤)) : D.left.K ⟶ D.target.K where
  f n := rightZeroComponent D y n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hd : (D.right.K.d 0 1).val.app V
        ((D.right.augmentation.f 0).val.app V
          (G.presheaf.map (homOfLE le_top).op y)) = 0 := by
      exact congrArg (fun t ↦ t.val.app V (G.presheaf.map (homOfLE le_top).op y))
        (CochainComplex.ι_f_zero_comp_d_zero_one_of_single₀ D.right.augmentation)
    have h := D.leibniz n 0 V.unop a
      ((D.right.augmentation.f 0).val.app V (G.presheaf.map (homOfLE le_top).op y))
    simp only [hd, map_zero, smul_zero, add_zero, eqToHom_refl] at h
    exact h
private def rightSectionMap {X : Scheme.{w}} (F G : X.Modules) (y : Γ(G, ⊤)) :
    F ⟶ F ⊗ G := (ρ_ F).inv ≫ (F ◁ homOfGlobalSection G y)

private theorem rightSectionMap_apply {X : Scheme.{w}} (F G : X.Modules)
    (y : Γ(G, ⊤)) (V : X.Opens) (a : Γ(F, V)) :
    (rightSectionMap F G y).app V a =
      tmulSection a (G.presheaf.map (homOfLE le_top).op y) := by
  simp only [rightSectionMap, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [rightUnitor_inv_app, whiskerLeft_app_tmulSection]
  congr 1
  exact homOfGlobalSection_app_one G y V

private theorem rightZeroMap_over {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (y : Γ(G, ⊤)) :
    D.left.augmentation ≫ rightZeroMap D y =
      (CochainComplex.single₀ X.Modules).map (rightSectionMap F G y) ≫
        D.target.augmentation := by
  apply HomologicalComplex.from_single_hom_ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change D.pair 0 0 V.unop ((D.left.augmentation.f 0).val.app V a)
    ((D.right.augmentation.f 0).val.app V (G.presheaf.map (homOfLE le_top).op y)) =
      (D.target.augmentation.f 0).val.app V ((rightSectionMap F G y).app V.unop a)
  exact (D.augmentation_pair V.unop a _).trans
    (congrArg ((D.target.augmentation.f 0).val.app V)
      (rightSectionMap_apply F G y V.unop a).symm)

private theorem scalarTensorCoefficient_rightSection
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (y : Γ(G, ⊤)) :
    (ρ_ (scalarSheaf f F)).inv ≫
        ((scalarSheaf f F) ◁ (scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection G y))) ≫
        scalarTensorCoefficient f F G = scalarHom f (rightSectionMap F G y) := by
  let U := SheafOfModules.unit X.ringCatSheaf
  have hi : scalarHom f (𝟙 F) = 𝟙 (scalarSheaf f F) := (scalarFunctor f).map_id F
  have hn := tensorCoefficient_naturality k X f F U F G (𝟙 F) (homOfGlobalSection G y)
  simp only [hi, tensorHom_def, id_whiskerRight, Category.id_comp] at hn
  have hu := (scalarTensorCoefficient_unit f F).1
  have hu' : ((scalarSheaf f F) ◁ scalarUnitMorphism f) ≫
      scalarTensorCoefficient f F U =
      (ρ_ (scalarSheaf f F)).hom ≫ scalarHom f (ρ_ F).inv := by
    have h := congrArg (fun t ↦ t ≫ scalarHom f (ρ_ F).inv) hu
    have hcancel : scalarHom f (ρ_ F).hom ≫ scalarHom f (ρ_ F).inv = 𝟙 _ := by
      change (scalarFunctor f).map (ρ_ F).hom ≫
        (scalarFunctor f).map (ρ_ F).inv = 𝟙 _
      rw [← Functor.map_comp, Iso.hom_inv_id]
      exact (scalarFunctor f).map_id _
    simp only [Category.assoc, hcancel] at h
    change ((_ ◁ _) ≫ scalarTensorCoefficient f F U) ≫ 𝟙 _ = _ at h
    exact (Category.comp_id _).symm.trans h
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hn]
  rw [← Category.assoc ((scalarSheaf f F) ◁ scalarUnitMorphism f)
    (scalarTensorCoefficient f F U), hu']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ((scalarFunctor f).map_comp (ρ_ F).inv (F ◁ homOfGlobalSection G y)).symm

private theorem scalarCup_right_zero
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G 0) :
    scalarCohomologyCup f F G p 0 a b =
      scalarCohomologyMap f (rightSectionMap F G (scalarGlobalSectionsEquiv f G b)) p a := by
  apply (scalarCohomologyExtEquiv f (@id X.Modules (F ⊗ G)) p).injective
  rw [scalarCohomologyExtEquiv_map]
  unfold scalarCohomologyCup
  refine ((scalarCohomologyExtEquiv f (@id X.Modules (F ⊗ G)) p).apply_symm_apply _).trans ?_
  rw [scalarCohomologyExtEquiv_zero_globalSections, scalarExtCup_right_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  exact congrArg (fun φ ↦ ((scalarCohomologyExtEquiv f F p) a).comp
    (Abelian.Ext.mk₀ φ) (add_zero p))
      ((Category.assoc _ _ _).trans
        (scalarTensorCoefficient_rightSection f F G (scalarGlobalSectionsEquiv f G b)))

private theorem scalarCup_resolution_right_zero
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p : ℕ)
    (D : CupResolutionPairing F G)
    (a : ResolutionCycles D.left p) (b : ResolutionCycles D.right 0)
    (c : ResolutionCycles D.target p) (hc : c.val = D.pair p 0 ⊤ a.val b.val) :
    scalarCohomologyCup f F G p 0 (D.left.class p a) (D.right.class 0 b) =
      D.target.class p c := by
  let y := scalarGlobalSectionsEquiv f G (D.right.class 0 b)
  have hb : (D.right.augmentation.f 0).val.app (op ⊤) y = b.val :=
    congrArg Subtype.val (augmentationCycle_eq f D.right b)
  have htop : G.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op y = y := by
    exact ConcreteCategory.congr_hom (G.presheaf.map_id (op ⊤)) y
  have hb' := (congrArg ((D.right.augmentation.f 0).val.app (op ⊤)) htop).trans hb
  have hc' : c.val = ((rightZeroMap D y).f p).val.app (op ⊤) a.val :=
    hc.trans (congrArg (fun t ↦ D.pair p 0 ⊤ a.val t) hb'.symm)
  have hn := computingClass_naturality D.left D.target (rightSectionMap F G y)
    (rightZeroMap D y) (rightZeroMap_over D y) p a c hc'
  exact (scalarCup_right_zero f F G p (D.left.class p a) (D.right.class 0 b)).trans hn.symm


private theorem ext_unit_comp {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} {n m : ℕ} (h : n = m) (a : Abelian.Ext X Y n) (v : Y ⟶ Z) :
    (Abelian.Ext.mk₀ (𝟙 X)).comp (a.comp (Abelian.Ext.mk₀ v) (add_zero n))
        (by omega : 0 + n = m) =
      a.comp (Abelian.Ext.mk₀ v) (by omega : n + 0 = m) := by
  subst m
  exact Abelian.Ext.mk₀_id_comp _

private theorem scalarExtCup_left_mk₀
    {k : Type w} [Field k] {X : Scheme.{w}} {A B : KSheaf X k} {n : ℕ}
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B n)
    (v : 𝟙_ (KSheaf X k) ⟶ A) :
    scalarExtCup (Abelian.Ext.mk₀ v) a =
      a.comp (Abelian.Ext.mk₀ ((λ_ B).inv ≫ (v ▷ B)))
        (by omega : n + 0 = 0 + n) := by
  have : EnoughInjectives (KSheaf X k) := inferInstance
  unfold scalarExtCup
  rw [Abelian.Ext.mapExactFunctor_mk₀]
  change ((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
    (Abelian.Ext.mk₀ (v ▷ (𝟙_ (KSheaf X k)))) (zero_add 0)).comp
    (a.mapExactFunctor (tensorLeft A)) rfl = _
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  have hn := ext_naturality (tensorLeft (𝟙_ (KSheaf X k))) (tensorLeft A)
    ((tensoringLeft (KSheaf X k)).map v) a
  change (a.mapExactFunctor (tensorLeft (𝟙_ (KSheaf X k)))).comp
      (Abelian.Ext.mk₀ (v ▷ B)) (add_zero n) =
    (Abelian.Ext.mk₀ (v ▷ (𝟙_ (KSheaf X k)))).comp
      (a.mapExactFunctor (tensorLeft A)) (zero_add n) at hn
  rw [← hn]
  rw [ext_iso_transport (tensorLeft (𝟙_ (KSheaf X k)))
    (leftUnitorNatIso (KSheaf X k)) a]
  simp only [leftUnitorNatIso, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀]
  exact ext_unit_comp (Nat.zero_add n).symm a ((λ_ B).inv ≫ (v ▷ B))

private def leftZeroRaw {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (x : Γ(F, ⊤)) (n : ℕ) :
    D.right.K.X n ⟶ D.target.K.X (0 + n) where
  val := {
    app := fun V ↦ ModuleCat.ofHom
      (D.pair 0 n V.unop ((D.left.augmentation.f 0).val.app V
        (F.presheaf.map (homOfLE le_top).op x)))
    naturality := by
      intro V W u
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change D.pair 0 n W.unop ((D.left.augmentation.f 0).val.app W
        (F.presheaf.map (homOfLE le_top).op x)) ((D.right.K.X n).val.map u a) =
          (D.target.K.X (0 + n)).val.map u
            (D.pair 0 n V.unop ((D.left.augmentation.f 0).val.app V
              (F.presheaf.map (homOfLE le_top).op x)) a)
      have hrest := D.restriction 0 n V.unop W.unop (leOfHom u.unop)
        ((D.left.augmentation.f 0).val.app V (F.presheaf.map (homOfLE le_top).op x)) a
      refine Eq.trans ?_ hrest.symm
      apply congrArg (fun t ↦ D.pair 0 n W.unop t ((D.right.K.X n).val.map u a))
      have haug := Hom.app_presheaf_map (D.left.augmentation.f 0) u.unop
        (F.presheaf.map (homOfLE le_top).op x)
      have hpres : F.presheaf.map u (F.presheaf.map (homOfLE le_top).op x) =
          F.presheaf.map (homOfLE le_top).op x := by
        exact (presheaf_map_map_apply (M := F) (homOfLE le_top) u.unop x).trans rfl
      exact (congrArg ((D.left.augmentation.f 0).val.app W) hpres.symm).trans haug }

private def leftZeroComponent {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (x : Γ(F, ⊤)) (n : ℕ) :
    D.right.K.X n ⟶ D.target.K.X n :=
  leftZeroRaw D x n ≫ eqToHom (congrArg (fun j ↦ D.target.K.X j) (Nat.zero_add n))

private theorem leftZeroRaw_comm {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (x : Γ(F, ⊤)) (n : ℕ) :
    leftZeroRaw D x n ≫ D.target.K.d (0 + n) (0 + n + 1) =
      D.right.K.d n (n + 1) ≫ leftZeroRaw D x (n + 1) ≫
        eqToHom (congrArg D.target.K.X (by omega : 0 + (n + 1) = 0 + n + 1)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hd : (D.left.K.d 0 1).val.app V
      ((D.left.augmentation.f 0).val.app V
        (F.presheaf.map (homOfLE le_top).op x)) = 0 := by
    exact congrArg (fun t ↦ t.val.app V (F.presheaf.map (homOfLE le_top).op x))
      (CochainComplex.ι_f_zero_comp_d_zero_one_of_single₀ D.left.augmentation)
  have h := D.leibniz 0 n V.unop
    ((D.left.augmentation.f 0).val.app V (F.presheaf.map (homOfLE le_top).op x)) a
  simp only [hd, map_zero, LinearMap.zero_apply, pow_zero, one_smul] at h
  exact h.trans (zero_add _)

private def leftZeroMap {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (x : Γ(F, ⊤)) : D.right.K ⟶ D.target.K where
  f n := leftZeroComponent D x n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    dsimp only [leftZeroComponent]
    rw [Category.assoc, ← eqToHom_naturality
      (fun i ↦ D.target.K.d i (i + 1)) (Nat.zero_add n),
      ← Category.assoc, leftZeroRaw_comm]
    simp only [Category.assoc, eqToHom_trans]


private def leftSectionMap {X : Scheme.{w}} (F G : X.Modules) (x : Γ(F, ⊤)) :
    G ⟶ F ⊗ G := (λ_ G).inv ≫ (homOfGlobalSection F x ▷ G)

private theorem leftSectionMap_apply {X : Scheme.{w}} (F G : X.Modules)
    (x : Γ(F, ⊤)) (V : X.Opens) (a : Γ(G, V)) :
    (leftSectionMap F G x).app V a =
      tmulSection (F.presheaf.map (homOfLE le_top).op x) a := by
  simp only [leftSectionMap, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [leftUnitor_inv_app]
  exact (whiskerRight_app_tmulSection (homOfGlobalSection F x) (unitSectionsEquiv V 1) a).trans
    (congrArg (fun s ↦ tmulSection s a) (homOfGlobalSection_app_one F x V))

private theorem leftZeroMap_over {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (x : Γ(F, ⊤)) :
    D.right.augmentation ≫ leftZeroMap D x =
      (CochainComplex.single₀ X.Modules).map (leftSectionMap F G x) ≫
        D.target.augmentation := by
  apply HomologicalComplex.from_single_hom_ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change D.pair 0 0 V.unop
    ((D.left.augmentation.f 0).val.app V (F.presheaf.map (homOfLE le_top).op x))
    ((D.right.augmentation.f 0).val.app V a) =
      (D.target.augmentation.f 0).val.app V ((leftSectionMap F G x).app V.unop a)
  exact (D.augmentation_pair V.unop _ a).trans
    (congrArg ((D.target.augmentation.f 0).val.app V)
      (leftSectionMap_apply F G x V.unop a).symm)

private theorem scalarTensorCoefficient_leftSection
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (x : Γ(F, ⊤)) :
    (λ_ (scalarSheaf f G)).inv ≫
        ((scalarUnitMorphism f ≫ scalarHom f (homOfGlobalSection F x)) ▷
          (scalarSheaf f G)) ≫ scalarTensorCoefficient f F G =
      scalarHom f (leftSectionMap F G x) := by
  let U := SheafOfModules.unit X.ringCatSheaf
  have hi : scalarHom f (𝟙 G) = 𝟙 (scalarSheaf f G) := (scalarFunctor f).map_id G
  have hn := tensorCoefficient_naturality k X f U G F G (homOfGlobalSection F x) (𝟙 G)
  simp only [hi, tensorHom_def, whiskerLeft_id, Category.comp_id] at hn
  have hu := (scalarTensorCoefficient_unit f G).2
  have hu' : (scalarUnitMorphism f ▷ (scalarSheaf f G)) ≫
      scalarTensorCoefficient f U G =
      (λ_ (scalarSheaf f G)).hom ≫ scalarHom f (λ_ G).inv := by
    have h := congrArg (fun t ↦ t ≫ scalarHom f (λ_ G).inv) hu
    have hcancel : scalarHom f (λ_ G).hom ≫ scalarHom f (λ_ G).inv = 𝟙 _ := by
      change (scalarFunctor f).map (λ_ G).hom ≫
        (scalarFunctor f).map (λ_ G).inv = 𝟙 _
      rw [← Functor.map_comp, Iso.hom_inv_id]
      exact (scalarFunctor f).map_id _
    simp only [Category.assoc, hcancel] at h
    change ((_ ▷ _) ≫ scalarTensorCoefficient f U G) ≫ 𝟙 _ = _ at h
    exact (Category.comp_id _).symm.trans h
  simp only [comp_whiskerRight, Category.assoc]
  rw [hn]
  rw [← Category.assoc (scalarUnitMorphism f ▷ (scalarSheaf f G))
    (scalarTensorCoefficient f U G), hu']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ((scalarFunctor f).map_comp (λ_ G).inv (homOfGlobalSection F x ▷ G)).symm


private theorem scalarExt_comp_cast
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) {n m : ℕ} (h : n = m)
    {A : KSheaf X k} (u : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A n)
    (v : A ⟶ scalarSheaf f F) (z : scalarCohomology f F n)
    (hz : scalarCohomologyExtEquiv f F n z = u.comp (Abelian.Ext.mk₀ v) (add_zero n)) :
    u.comp (Abelian.Ext.mk₀ v) (by omega : n + 0 = m) =
      scalarCohomologyExtEquiv f F m
        (cast (congrArg (fun j ↦ ↥(scalarCohomology f F j)) h) z) := by
  subst m
  exact hz.symm

private theorem scalarCup_left_zero
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (q : ℕ)
    (a : scalarCohomology f F 0) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G 0 q a b =
      cast (congrArg (fun n ↦ ↥(scalarCohomology f (@id X.Modules (F ⊗ G)) n))
        (Nat.zero_add q).symm)
        (scalarCohomologyMap f (leftSectionMap F G (scalarGlobalSectionsEquiv f F a)) q b) := by
  have hq : 0 + q = q := Nat.zero_add q
  apply (scalarCohomologyExtEquiv f (@id X.Modules (F ⊗ G)) (0 + q)).injective
  unfold scalarCohomologyCup
  refine ((scalarCohomologyExtEquiv f (@id X.Modules (F ⊗ G)) (0 + q)).apply_symm_apply
    _).trans ?_
  rw [scalarCohomologyExtEquiv_zero_globalSections,
    scalarExtCup_left_mk₀]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  have ht := scalarTensorCoefficient_leftSection f F G (scalarGlobalSectionsEquiv f F a)
  have hc := congrArg (fun φ ↦ ((scalarCohomologyExtEquiv f G q) b).comp
    (Abelian.Ext.mk₀ φ) (by omega : q + 0 = 0 + q))
      ((Category.assoc _ _ _).trans ht)
  refine hc.trans ?_
  have he := scalarCohomologyExtEquiv_map f
    (leftSectionMap F G (scalarGlobalSectionsEquiv f F a)) q b
  exact scalarExt_comp_cast f (@id X.Modules (F ⊗ G)) (Nat.zero_add q).symm
    ((scalarCohomologyExtEquiv f G q) b)
    (scalarHom f (leftSectionMap F G (scalarGlobalSectionsEquiv f F a))) _ he


private def cycleCast {X : Scheme.{w}} {F : X.Modules} (D : CupAcyclicResolution F)
    {n m : ℕ} (h : n = m) (a : ResolutionCycles D n) : ResolutionCycles D m :=
  cast (congrArg (fun j ↦ ↥(ResolutionCycles D j)) h) a

private theorem cycleCast_val {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) {n m : ℕ} (h : n = m) (a : ResolutionCycles D n) :
    (cycleCast D h a).val =
      (eqToHom (congrArg D.K.X h)).val.app (op ⊤) a.val := by
  subst m
  rfl

private theorem cycleCast_class_cancel {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) {n m : ℕ} (h : n = m) (a : ResolutionCycles D n) :
    cast (congrArg (fun j ↦ ↥((RingedSpace.moduleCohomology X.toRingedSpace j).obj F))
      h.symm) (D.class m (cycleCast D h a)) = D.class n a := by
  subst m
  rfl

private theorem scalarCup_resolution_left_zero
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ResolutionCycles D.left 0) (b : ResolutionCycles D.right q)
    (c : ResolutionCycles D.target (0 + q)) (hc : c.val = D.pair 0 q ⊤ a.val b.val) :
    scalarCohomologyCup f F G 0 q (D.left.class 0 a) (D.right.class q b) =
      D.target.class (0 + q) c := by
  let x := scalarGlobalSectionsEquiv f F (D.left.class 0 a)
  have ha : (D.left.augmentation.f 0).val.app (op ⊤) x = a.val :=
    congrArg Subtype.val (augmentationCycle_eq f D.left a)
  have htop : F.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x := by
    exact ConcreteCategory.congr_hom (F.presheaf.map_id (op ⊤)) x
  have ha' := (congrArg ((D.left.augmentation.f 0).val.app (op ⊤)) htop).trans ha
  let c' := cycleCast D.target (Nat.zero_add q) c
  have hc' : c'.val = ((leftZeroMap D x).f q).val.app (op ⊤) b.val := by
    exact (cycleCast_val D.target (Nat.zero_add q) c).trans
      (congrArg
        ((eqToHom (congrArg D.target.K.X (Nat.zero_add q))).val.app (op ⊤))
        (hc.trans (congrArg (fun t ↦ D.pair 0 q ⊤ t b.val) ha'.symm)))
  have hn := computingClass_naturality D.right D.target (leftSectionMap F G x)
    (leftZeroMap D x) (leftZeroMap_over D x) q b c' hc'
  refine (scalarCup_left_zero f F G q (D.left.class 0 a) (D.right.class q b)).trans ?_
  exact (congrArg
    (cast (congrArg (fun j ↦ ↥(scalarCohomology f (@id X.Modules (F ⊗ G)) j))
      (Nat.zero_add q).symm)) hn.symm).trans
        (cycleCast_class_cancel D.target (Nat.zero_add q) c)

end

/-- The scalar Ext cup is represented by the paired cycle of a module resolution.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV, resolution cup comparison.
(blueprint: new-sc-scalar-cup-resolution-class-compatibility).

Proof: Split on the right degree q. For q=0, the degree-zero class map is
injective, so b is the augmentation of its corresponding global section y.
The map x ↦ D.pair n 0 x y is a genuine map of resolutions: restrictions give
naturality and Leibniz with dy=0 gives the chain equation. It lies over the
coefficient map F → F tensor G obtained by tensoring with y. The injective
comparison theorem and homology naturality identify its class map with the
coefficient map on cohomology. Exact-functor transport along the right unitor
identifies scalarExtCup with postcomposition by this coefficient map, giving
the equality; the sign is 1. For p=0, construct the analogous map using the
left augmentation and the left unitor; explicit degree casts transport 0+q to q.
For p,q>0 apply the positive-degree comparison, whose docstring records the
total-tensor and shift calculation.
The argument includes degree zero, zero coefficients, and empty schemes.

The Yoneda product applies the left class first. Moving that shift out before the
right shift multiplies the unsigned (p,q) tensor summand by (-1)^(p*q). Thus the
resolution class on the right carries this Koszul factor. The original module's
private audit checked the order and the nontrivial degree-(1,1) case over Q;
those checks are no longer needed by this proof.
-/
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      (-1 : ℤ) ^ (p * q) • D.target.class (p + q) c := by
  cases q with
  | zero =>
    have h := scalarCup_resolution_right_zero f F G p D a b c hc
    exact h.trans (one_smul ℤ (D.target.class p c)).symm
  | succ q =>
    cases p with
    | zero =>
      have h := scalarCup_resolution_left_zero f F G (q + 1) D a b c hc
      have hs : (-1 : ℤ) ^ (0 * (q + 1)) = 1 := by simp
      exact h.trans ((congrArg (fun r : ℤ ↦ r • D.target.class (0 + (q + 1)) c) hs).trans
        (one_smul ℤ _)).symm
    | succ p =>
      exact scalarCup_positive_resolution_class_compatibility f F G (p + 1) (q + 1)
        (Nat.succ_pos p) (Nat.succ_pos q) D a b c hc



end AlgebraicGeometry.Scheme.Modules
