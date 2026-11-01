/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # The intrinsic regular-unit restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local instance 6000] finiteDualizingSiteSmall
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem inclusion_unit
    (J : GrothendieckTopology W.ProEt) (A : Type (u + 1)) [CommRing A] :
    Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{u + 1} A)) =
      toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of A A)) := by
  rw [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  have h : Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{u + 1} A)) =
      𝟙 _ := rfl
  rw [h]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem fixed_restriction_one
    (J : GrothendieckTopology W.ProEt) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (U : W.ProEtᵒᵖ) :
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars J φ)).hom.app U
      ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U
        (1 : A)) =
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of B B))).app U
        (1 : B) := by
  have h := congrArg (fun z ↦ (z.app U) (1 : A))
    (Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose J
      (ModuleCat.restrictScalars φ))
  rw [inclusion_unit W J A, inclusion_unit W J B] at h
  change (Functor.LaxMonoidal.ε (Sheaf.restrictScalars J φ)).hom.app U
    ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U (1 : A)) =
    (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of B B))).app U
      (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars φ) (1 : A)) at h
  simpa only [ModuleCat.restrictScalars_η, map_one] using h

private theorem realization_map_unit {A : Type u} [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.obj.obj U) :
    ((sfIntrinsicModuleEquivalence W A).functor.map f).val.app U
      (sfIntrinsicRealizationUnit W A M U x) =
    sfIntrinsicRealizationUnit W A N U (f.hom.app U x) := by
  unfold sfIntrinsicModuleEquivalence
  exact (congrArg (fun z ↦ z.app U x)
    ((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap W A)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf W.ProEt (ULift.{u + 1, u} A)).map
          f.hom))).symm

private def restriction_unit_map
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S) :
    SheafOfModules.unit R ⟶ (SheafOfModules.restrictScalars φ).obj
      (SheafOfModules.unit S) where
  val.app U := ModuleCat.ofHom
    (X := (SheafOfModules.unit R).val.obj U)
    (Y := ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit S)).val.obj U)
    { toFun := fun x ↦ φ.hom.app U x
      map_add' := fun x y ↦ (φ.hom.app U).hom.map_add x y
      map_smul' := fun x y ↦ (φ.hom.app U).hom.map_mul x y }
  val.naturality f := ModuleCat.hom_ext (LinearMap.ext fun x ↦
    ConcreteCategory.congr_hom (φ.hom.naturality f) x)

private abbrev intrinsicRing (A : Type u) [CommRing A] :=
  (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing W A)

private def fixedOne (A : Type u) [CommRing A] (U : W.ProEtᵒᵖ) :
    (𝟙_ (Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj.obj U :=
  (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app U (1 : ULift.{u + 1, u} A)

set_option maxHeartbeats 2000000 in
-- Compare the maps on scalar-unit sections before deriving them.
attribute [local irreducible] sfIntrinsicModuleEquivalence in
private theorem intrinsic_unit_square_generic
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (a : (sfIntrinsicModuleEquivalence W A).functor.obj (𝟙_ _) ≅
      SheafOfModules.unit (intrinsicRing W A))
    (b : (sfIntrinsicModuleEquivalence W B).functor.obj (𝟙_ _) ≅
      SheafOfModules.unit (intrinsicRing W B))
    (ha : ∀ U : W.ProEtᵒᵖ, a.hom.val.app U
      (sfIntrinsicRealizationUnit W A (𝟙_ _) U (fixedOne W A U)) =
        (1 : (intrinsicRing W A).obj.obj U))
    (hb : ∀ U : W.ProEtᵒᵖ, b.hom.val.app U
      (sfIntrinsicRealizationUnit W B (𝟙_ _) U (fixedOne W B U)) =
        (1 : (intrinsicRing W B).obj.obj U)) :
    let c := (finiteDualizingRestriction_existsUnique W φ).choose
    let R := finiteDualizingIntrinsicRes W φ
    (sfIntrinsicModuleEquivalence W A).functor.map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
          (RingHom.ulift.{u + 1, u + 1} φ))) ≫
      c.inv.app (𝟙_ _) ≫ R.map b.hom =
    a.hom ≫ restriction_unit_map (finiteDualizingIntrinsicRingMap W φ) := by
  dsimp only
  let c := (finiteDualizingRestriction_existsUnique W φ).choose
  let R := finiteDualizingIntrinsicRes W φ
  let ε := Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
    (RingHom.ulift.{u + 1, u + 1} φ))
  let F := (sfIntrinsicModuleEquivalence W A).functor
  let q := restriction_unit_map (finiteDualizingIntrinsicRingMap W φ)
  change F.map ε ≫ c.inv.app (𝟙_ _) ≫ R.map b.hom = a.hom ≫ q
  apply (cancel_epi a.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext U
  let xm := sfIntrinsicRealizationUnit W A (𝟙_ _) U (fixedOne W A U)
  let xn := sfIntrinsicRealizationUnit W B (𝟙_ _) U (fixedOne W B U)
  have ha' : a.hom.val.app U xm = (1 : (intrinsicRing W A).obj.obj U) := ha U
  have hb' : b.hom.val.app U xn = (1 : (intrinsicRing W B).obj.obj U) := hb U
  have hai : a.inv.val.app U (1 : (intrinsicRing W A).obj.obj U) = xm := by
    rw [← ha']
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app U) a.hom_inv_id) xm
  have hc := (finiteDualizingRestriction_existsUnique W φ).choose_spec.1
    (𝟙_ _) U (fixedOne W B U)
  have hci : (c.inv.app (𝟙_ _)).val.app U
      (sfIntrinsicRealizationUnit W A
        ((Sheaf.restrictScalars (ProEt.topology W) (RingHom.ulift.{u + 1, u + 1} φ)).obj (𝟙_ _)) U
        (fixedOne W B U)) = xn := by
    rw [← eq_of_heq hc]
    have hc' := congrArg (fun f ↦ f.val.app U) (c.hom_inv_id_app (𝟙_ _))
    have hx := ConcreteCategory.congr_hom hc' xn
    change (c.inv.app (𝟙_ _)).val.app U
      ((c.hom.app (𝟙_ _)).val.app U xn) = xn at hx
    exact hx
  have he : ε.hom.app U (fixedOne W A U) = fixedOne W B U :=
    fixed_restriction_one W (ProEt.topology W) (RingHom.ulift.{u + 1, u + 1} φ) U
  change b.hom.val.app U ((c.inv.app (𝟙_ _)).val.app U
    ((F.map ε).val.app U (a.inv.val.app U (1 : (intrinsicRing W A).obj.obj U)))) =
    (finiteDualizingIntrinsicRingMap W φ).hom.app U (1 : (intrinsicRing W A).obj.obj U)
  rw [hai, realization_map_unit, he, hci, hb']
  exact ((finiteDualizingIntrinsicRingMap W φ).hom.app U).hom.map_one.symm

private theorem exact_square_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) (G : B ⥤ D) (U : B ⥤ A) (V : D ⥤ C)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : U ⋙ F ≅ G ⋙ V) (M : B) :
    (Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor B 0).obj M) ≫
      V.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) =
    F.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem exact_square_regular
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) (G : B ⥤ D) (U : B ⥤ A) (V : D ⥤ C)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : U ⋙ F ≅ G ⋙ V) {M : A} {N : B} {P : C} {Q : D}
    (a : F.obj M ≅ P) (b : G.obj N ≅ Q)
    (f : M ⟶ U.obj N) (q : P ⟶ V.obj Q)
    (ho : F.map f ≫ e.hom.app N ≫ V.map b.hom = a.hom ≫ q) :
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map f ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor B 0).obj N) ≫
      V.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map b.hom) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app Q =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map (a.hom ≫ q) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(V.mapDerivedCategorySingleFunctor 0).hom.naturality b.hom]
  erw [reassoc_of% (exact_square_single F G U V e N)]
  rw [← F.mapDerivedCategory.map_comp_assoc, ← F.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [reassoc_of% ((F.mapDerivedCategorySingleFunctor 0).hom.naturality f)]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [ho]

private theorem exact_square_regular_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) (G : B ⥤ D) (U : B ⥤ A) (V : D ⥤ C)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : G ⋙ V ≅ U ⋙ F) {M : A} {N : B} {P : C} {Q : D}
    (a : F.obj M ≅ P) (b : G.obj N ≅ Q)
    (f : M ⟶ U.obj N) (q : P ⟶ V.obj Q)
    (ho : F.map f ≫ e.inv.app N ≫ V.map b.hom = a.hom ≫ q) :
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map f ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (Functor.mapDerivedCategorySquareIso e).inv.app
        ((DerivedCategory.singleFunctor B 0).obj N) ≫
      V.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map b.hom) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app Q =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map a.hom ≫
      (DerivedCategory.singleFunctor C 0).map q := by
  simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Functor.map_comp, Category.assoc] using
    exact_square_regular F G U V e.symm a b f q ho

-- Fix the small source localization once with abstract coefficients.
@[instance_reducible] private def fixedModuleHasDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  inferInstance

attribute [local instance 100001] fixedModuleHasDerived
attribute [local implicit_reducible] fixedModuleHasDerived

-- Keep exact derived models fixed while normalizing comparison coordinates.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] scalarReductionTargetDerived
  finiteDualizingRealization

attribute [local implicit_reducible] Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  sfIntrinsicDerivedEquivalence integralCoefficientSheaf Etale.constantComplex
  SheafOfModules.unit PresheafOfModules.unit ExistsUnique ProEtale.pbcFixedScalarExtension
  reductionModulesHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private def fixedGenericCoordinates (A : Type u) [CommRing A] [Finite A]
    (a : (sfIntrinsicModuleEquivalence W A).functor.obj (𝟙_ _) ≅
      SheafOfModules.unit (intrinsicRing W A)) :=
  (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 2}
    (sfIntrinsicModuleEquivalence W A).functor 0).app (𝟙_ _) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso a

set_option maxHeartbeats 4000000 in
-- The comparison transports both the small and standard derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem intrinsic_generic_derived_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (a : (sfIntrinsicModuleEquivalence W A).functor.obj (𝟙_ _) ≅
      SheafOfModules.unit (intrinsicRing W A))
    (b : (sfIntrinsicModuleEquivalence W B).functor.obj (𝟙_ _) ≅
      SheafOfModules.unit (intrinsicRing W B))
    (ho : (sfIntrinsicModuleEquivalence W A).functor.map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
          (RingHom.ulift.{u + 1, u + 1} φ))) ≫
      (finiteDualizingRestriction_existsUnique W φ).choose.inv.app (𝟙_ _) ≫
        (finiteDualizingIntrinsicRes W φ).map b.hom =
      a.hom ≫ restriction_unit_map (finiteDualizingIntrinsicRingMap W φ)) :
    (sfIntrinsicDerivedEquivalence W A).functor.map
        ((DerivedCategory.singleFunctor _ 0).map
            (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
              (RingHom.ulift.{u + 1, u + 1} φ))) ≫
          ((Sheaf.restrictScalars (ProEt.topology W)
            (RingHom.ulift.{u + 1, u + 1} φ)).mapDerivedCategorySingleFunctor 0).inv.app
              (𝟙_ _)) ≫
      (finiteDualizingGenericDerivedRestriction W φ).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≫
      (finiteDualizingIntrinsicRes W φ).mapDerivedCategory.map
        (fixedGenericCoordinates W B b).hom ≫
      ((finiteDualizingIntrinsicRes W φ).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (intrinsicRing W B)) =
    (fixedGenericCoordinates W A a).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (restriction_unit_map (finiteDualizingIntrinsicRingMap W φ)) := by
  have hd := exact_square_regular_inv.{u + 2, u + 2, u + 2, u + 2,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
    (sfIntrinsicModuleEquivalence W A).functor
    (sfIntrinsicModuleEquivalence W B).functor
    (Sheaf.restrictScalars (ProEt.topology W) (RingHom.ulift.{u + 1, u + 1} φ))
    (finiteDualizingIntrinsicRes W φ)
    (finiteDualizingRestriction_existsUnique W φ).choose a b
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
      (RingHom.ulift.{u + 1, u + 1} φ)))
    (restriction_unit_map (finiteDualizingIntrinsicRingMap W φ)) ho
  simp only [fixedGenericCoordinates, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    finiteDualizingGenericDerivedRestriction, sfIntrinsicDerivedEquivalence,
    Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk,
    Functor.map_comp, Category.assoc] at hd ⊢
  exact hd

attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private def fixedCoordinates (n : ℕ) :=
  fixedGenericCoordinates W (Padic.coefficientExtensionRing l E (n + 1))
    (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose

set_option maxHeartbeats 4000000 in
-- The comparison transports both the small and standard derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
attribute [-instance] fixedModuleHasDerived in
/-- The generator-normalized intrinsic realization carries the derived restriction unit
onto the map of regular modules that sends 1 to 1.
Source: blueprint finite mapping-complex comparison, proof paragraph 2.
(blueprint: new-lem-coef-integral-unit-intrinsic-square).
Proof: unitHomEquiv identifies the supplied map with the actual coefficient-ring map.
The scalar-unit normalization of the realization and restriction comparison makes
its ordinary unit square commute, by evaluation on 1. Exact single-functor
coherence derives that square. Finally transport the coefficient ring map and the
comparison along their specified equality and HEq. This also covers equal levels
and the first positive quotient. -/
theorem integralDualizingIntrinsicUnit_restriction_square {m n : ℕ} (h : n ≤ m)
    (ψ : integralCoefficientSheaf l E W m ⟶ integralCoefficientSheaf l E W n)
    (hψ : ψ = finiteDualizingIntrinsicRingMap W (finiteDualizingQuotientBase l E h))
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} ψ)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} ψ)]
    (e : (sfIntrinsicDerivedEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        (SheafOfModules.restrictScalars ψ).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (ProEt.topology W) (finiteDualizingQuotient l E h) ⋙
        (sfIntrinsicDerivedEquivalence W
          (Padic.coefficientExtensionRing l E (m + 1))).functor)
    (he : HEq e (finiteDualizingGenericDerivedRestriction W
      (finiteDualizingQuotientBase l E h)))
    (q : SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (SheafOfModules.restrictScalars ψ).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
    (hq : ∀ U : W.ProEtᵒᵖ, q.val.app U
      (1 : (integralCoefficientSheaf l E W m).obj.obj U) =
        (1 : (integralCoefficientSheaf l E W n).obj.obj U)) :
    let cm :=
      (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 2}
        (sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (m + 1))).functor 0).app (𝟙_ _) ≪≫
        (DerivedCategory.singleFunctor
          (proEtaleRingModules W (proEtaleConstantRing W
            (Padic.coefficientExtensionRing l E (m + 1)))) 0).mapIso
              (finiteDualizingIntrinsicUnit_existsUnique l E W m).choose
    let cn :=
      (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 2}
        (sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).functor 0).app (𝟙_ _) ≪≫
        (DerivedCategory.singleFunctor
          (proEtaleRingModules W (proEtaleConstantRing W
            (Padic.coefficientExtensionRing l E (n + 1)))) 0).mapIso
              (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose
    (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((DerivedCategory.singleFunctor _ 0).map
            (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
              (finiteDualizingQuotient l E h))) ≫
          ((Sheaf.restrictScalars (ProEt.topology W)
            (finiteDualizingQuotient l E h)).mapDerivedCategorySingleFunctor 0).inv.app
              (𝟙_ _)) ≫
      e.inv.app ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≫
      (SheafOfModules.restrictScalars ψ).mapDerivedCategory.map
        cn.hom ≫
      ((SheafOfModules.restrictScalars ψ).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    cm.hom ≫
      (DerivedCategory.singleFunctor _ 0).map q := by
  change
    (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((DerivedCategory.singleFunctor _ 0).map
            (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
              (finiteDualizingQuotient l E h))) ≫
          ((Sheaf.restrictScalars (ProEt.topology W)
            (finiteDualizingQuotient l E h)).mapDerivedCategorySingleFunctor 0).inv.app
              (𝟙_ _)) ≫
      e.inv.app ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≫
      (SheafOfModules.restrictScalars ψ).mapDerivedCategory.map
        (fixedCoordinates l E W n).hom ≫
      ((SheafOfModules.restrictScalars ψ).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    (fixedCoordinates l E W m).hom ≫
      (DerivedCategory.singleFunctor _ 0).map q
  have hq' : q = restriction_unit_map ψ := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext U
    exact (hq U).trans ((ψ.hom.app U).hom.map_one.symm)
  subst q
  subst ψ
  have he' := eq_of_heq he
  subst e
  have ho := intrinsic_unit_square_generic W (finiteDualizingQuotientBase l E h)
    (finiteDualizingIntrinsicUnit_existsUnique l E W m).choose
    (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose
    (finiteDualizingIntrinsicUnit_existsUnique l E W m).choose_spec.1
    (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose_spec.1
  exact intrinsic_generic_derived_square W (finiteDualizingQuotientBase l E h)
      (finiteDualizingIntrinsicUnit_existsUnique l E W m).choose
      (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose ho


end WeilConjectures
