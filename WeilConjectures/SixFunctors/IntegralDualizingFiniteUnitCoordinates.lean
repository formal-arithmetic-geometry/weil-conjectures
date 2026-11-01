/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingFiniteUnitQuotient
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData

import WeilConjectures.SixFunctors.IntegralDualizingIntrinsicUnitSquare
import WeilConjectures.SixFunctors.IntegralDualizingSiteUnitSquare

/-! # Regular coordinates of the finite coefficient-unit quotient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u r
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

private def siteCoordinates (A : Type (u + 1)) [CommRing A] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory.mapIso
      (Etale.constantComplexIsoSingleFunctor A W) ≪≫
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategorySingleFunctor
      0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (ProEtale.comparisonUpperStarUnitIso A W)

private theorem site_unit_coordinates (A : Type (u + 1)) [CommRing A] :
    (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A W).hom ≫
      (DerivedCategory.singleFunctorObjUnitIso
        (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} A))).inv =
    (siteCoordinates W A).hom := by
  have he : (DerivedCategory.singleFunctorObjUnitIso
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))).inv =
      (Etale.constantComplexIsoSingleFunctor A W).hom := by
    exact (SheafExactDegreeZero.single_unit_inv).trans
      (Etale.singleFunctorObjUnitIso_inv (ModuleCat.{u + 1} A) W).symm
  dsimp only [ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso,
    siteCoordinates, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, he]

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
private def fixedCoordinates (n : ℕ) :=
  (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 2}
    (sfIntrinsicModuleEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor 0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor
      (proEtaleRingModules W (proEtaleConstantRing W
        (Padic.coefficientExtensionRing l E (n + 1)))) 0).mapIso
          (finiteDualizingIntrinsicUnit_existsUnique l E W n).choose

attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private def unitCoordinates (n : ℕ) :=
  (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
        (finiteDualizingCoeff l E n) W) ≪≫
    finiteDualizingIntrinsicUnit l E W n

attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem unitCoordinates_hom (n : ℕ) :
    (unitCoordinates l E W n).hom =
      (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (siteCoordinates W (finiteDualizingCoeff l E n)).hom ≫
        (fixedCoordinates l E W n).hom := by
  dsimp only [unitCoordinates, finiteDualizingIntrinsicUnit, fixedCoordinates,
    sfIntrinsicDerivedEquivalence, Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  erw [← (sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategory.map_comp_assoc,
    site_unit_coordinates]
  rfl

private theorem restriction_map_injective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (f g : R ⟶ S)
    (h : SheafOfModules.restrictScalars.{r} f = SheafOfModules.restrictScalars.{r} g) :
    f = g := by
  ext U x
  have hm := congrArg
    (fun F : SheafOfModules.{r} S ⥤ SheafOfModules.{r} R ↦
      (F.obj (SheafOfModules.unit S)).val.obj U) h
  have ha := congr_arg_heq
    (fun M : ModuleCat.{r} (R.obj.obj U) ↦
      fun a : R.obj.obj U ↦ fun b : M ↦ a • b) hm
  have hs : (fun a : R.obj.obj U ↦ fun b : S.obj.obj U ↦ (f.hom.app U).hom a * b) =
      (fun a : R.obj.obj U ↦ fun b : S.obj.obj U ↦ (g.hom.app U).hom a * b) :=
    eq_of_heq ha
  simpa only [mul_one] using congrFun (congrFun hs x) (1 : S.obj.obj U)

private theorem quotient_ring_eq {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient l E W h =
      finiteDualizingIntrinsicRingMap W (finiteDualizingQuotientBase l E h) := by
  exact restriction_map_injective (normalizedDVRQuotient l E W h)
    (finiteDualizingIntrinsicRingMap W (finiteDualizingQuotientBase l E h))
    (finiteDualizingRestriction_eq l E W h)

private theorem paste_unit_squares
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ C) (G : B ⥤ D) (U : B ⥤ A) (V : D ⥤ C)
    (e : G ⋙ V ≅ U ⋙ F) {X M : A} {Y N : B} {P : C} {Q : D} {O : C}
    (i : X ⟶ M) (j : Y ⟶ N) (t : X ⟶ U.obj Y) (f : M ⟶ U.obj N)
    (a : F.obj M ⟶ P) (b : G.obj N ⟶ Q) (k : V.obj Q ⟶ O) (r : P ⟶ O)
    (hs : t ≫ U.map j = i ≫ f)
    (hi : F.map f ≫ e.inv.app N ≫ V.map b ≫ k = a ≫ r) :
    F.map t ≫ e.inv.app Y ≫ V.map (G.map j ≫ b) ≫ k = (F.map i ≫ a) ≫ r := by
  have hn := e.inv.naturality j
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← F.map_comp_assoc, hs, F.map_comp]
  simp only [Category.assoc]
  rw [hi]

private theorem coordinates_of_paste
    {C D : Type*} [Category C] [Category D] (V : D ⥤ C)
    {X Z P O : C} {Y Q : D} {s : X ⟶ V.obj Y}
    {p : X ⟶ Z} {q : Z ⟶ V.obj Y}
    {a a' : X ⟶ P} {b b' : Y ⟶ Q} {k : V.obj Q ⟶ O} {r : P ⟶ O}
    (hs : s = p ≫ q) (ha : a = a') (hb : b = b')
    (hp : p ≫ q ≫ V.map b' ≫ k = a' ≫ r) :
    s ≫ V.map b ≫ k = a ≫ r := by
  subst s a b
  simpa only [Category.assoc] using hp

private theorem realization_restriction_form
    {Ae Be Ap Bp Ai Bi : Type*}
    [Category Ae] [Category Be] [Category Ap] [Category Bp] [Category Ai] [Category Bi]
    (Cm : Ae ⥤ Ap) (Cn : Be ⥤ Bp) (Sm : Ap ⥤ Ai) (Sn : Bp ⥤ Bi)
    (Re : Be ⥤ Ae) (Rp : Bp ⥤ Ap) (Ri : Bi ⥤ Ai)
    (e : Sn ⋙ Ri ≅ Rp ⋙ Sm) (c : Cn ⋙ Rp ≅ Re ⋙ Cm)
    {X : Ae} {Y : Be} (t : X ⟶ Re.obj Y) :
    (Cm ⋙ Sm).map t ≫
      (Functor.associator Cn Sn Ri ≪≫
        Functor.isoWhiskerLeft Cn e ≪≫
        (Functor.associator Cn Rp Sm).symm ≪≫
        Functor.isoWhiskerRight c Sm ≪≫
        Functor.associator Re Cm Sm).inv.app Y =
    Sm.map (Cm.map t ≫ c.inv.app Y) ≫ e.inv.app (Cn.obj Y) := by
  simp only [Functor.comp_map, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp]

set_option maxHeartbeats 4000000 in
-- Normalize the composite in the fixed exact derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem finite_unit_quotient_form {m n : ℕ} (h : n ≤ m) :
    integralDualizingFiniteUnitQuotient l E W h =
      (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
              W).mapDerivedCategory.map
            ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
              (finiteDualizingQuotient l E h))).homEquiv _ _
                (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) W).hom) ≫
            (ProEtale.pbcDerivedComparisonRestrict W (finiteDualizingQuotient l E h)).inv.app
              (Etale.constantComplex (finiteDualizingCoeff l E n) W)) ≫
        (finiteDualizingIntrinsicRestriction l E W h).inv.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
              W).mapDerivedCategory.obj
                (Etale.constantComplex (finiteDualizingCoeff l E n) W)) := by
  exact realization_restriction_form
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
      W).mapDerivedCategory
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
      W).mapDerivedCategory
    (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (m + 1))).functor
    (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (finiteDualizingQuotient l E h))
    (Sheaf.derivedRestrictScalars (ProEt.topology W) (finiteDualizingQuotient l E h))
    (normalizedDVRRes l E W h) (finiteDualizingIntrinsicRestriction l E W h)
    (ProEtale.pbcDerivedComparisonRestrict W (finiteDualizingQuotient l E h))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
      (finiteDualizingQuotient l E h))).homEquiv _ _
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) W).hom)

set_option maxHeartbeats 4000000 in
-- Apply the intrinsic comparison in its specified exact derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem intrinsic_unit_square {m n : ℕ} (h : n ≤ m)
    (q : SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (normalizedDVRModuleRes l E W h).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
    (hq : ∀ U : W.ProEtᵒᵖ, q.val.app U
      (1 : (integralCoefficientSheaf l E W m).obj.obj U) =
        (1 : (integralCoefficientSheaf l E W n).obj.obj U)) :
    (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((DerivedCategory.singleFunctor _ 0).map
            (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
              (finiteDualizingQuotient l E h))) ≫
          ((Sheaf.restrictScalars (ProEt.topology W)
            (finiteDualizingQuotient l E h)).mapDerivedCategorySingleFunctor 0).inv.app
              (𝟙_ _)) ≫
      (finiteDualizingIntrinsicRestriction l E W h).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (𝟙_ (Sheaf (ProEt.topology W)
            (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))))) ≫
      (normalizedDVRRes l E W h).map (fixedCoordinates l E W n).hom ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    (fixedCoordinates l E W m).hom ≫
      (DerivedCategory.singleFunctor _ 0).map q := by
  exact integralDualizingIntrinsicUnit_restriction_square l E W h
    (normalizedDVRQuotient l E W h)
    (quotient_ring_eq l E W h) (finiteDualizingIntrinsicRestriction l E W h)
    (finiteDualizingIntrinsicRestriction_existsUnique l E W h).choose_spec.1
    q hq

set_option maxHeartbeats 4000000 in
-- Paste the derived squares without unfolding their chosen localizations.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem pasted_unit_square {m n : ℕ} (h : n ≤ m)
    (q : SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (normalizedDVRModuleRes l E W h).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
    (hq : ∀ U : W.ProEtᵒᵖ, q.val.app U
      (1 : (integralCoefficientSheaf l E W m).obj.obj U) =
        (1 : (integralCoefficientSheaf l E W n).obj.obj U)) :
    (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
            W).mapDerivedCategory.map
          ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
            (finiteDualizingQuotient l E h))).homEquiv _ _
              (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) W).hom) ≫
          (ProEtale.pbcDerivedComparisonRestrict W (finiteDualizingQuotient l E h)).inv.app
            (Etale.constantComplex (finiteDualizingCoeff l E n) W)) ≫
      (finiteDualizingIntrinsicRestriction l E W h).inv.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
            W).mapDerivedCategory.obj
              (Etale.constantComplex (finiteDualizingCoeff l E n) W)) ≫
      (normalizedDVRRes l E W h).map
        ((sfIntrinsicDerivedEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).functor.map
            (siteCoordinates W (finiteDualizingCoeff l E n)).hom ≫
              (fixedCoordinates l E W n).hom) ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    ((sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        (siteCoordinates W (finiteDualizingCoeff l E m)).hom ≫
          (fixedCoordinates l E W m).hom) ≫
      (DerivedCategory.singleFunctor _ 0).map q := by
  let F : DerivedCategory
      (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))) ⥤
      normalizedDVRDerived l E W m :=
    (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (m + 1))).functor
  let G : DerivedCategory
      (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) ⥤
      normalizedDVRDerived l E W n :=
    (sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor
  have hd := intrinsic_unit_square l E W h q hq
  have hs := integralDualizingSiteUnit_restriction_square W (finiteDualizingQuotient l E h)
  exact paste_unit_squares F G
    (Sheaf.derivedRestrictScalars (ProEt.topology W) (finiteDualizingQuotient l E h))
    (normalizedDVRRes l E W h) (finiteDualizingIntrinsicRestriction l E W h)
    (siteCoordinates W (finiteDualizingCoeff l E m)).hom
    (siteCoordinates W (finiteDualizingCoeff l E n)).hom
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
        W).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
          (finiteDualizingQuotient l E h))).homEquiv _ _
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) W).hom) ≫
      (ProEtale.pbcDerivedComparisonRestrict W (finiteDualizingQuotient l E h)).inv.app
        (Etale.constantComplex (finiteDualizingCoeff l E n) W))
    ((DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W)
          (finiteDualizingQuotient l E h))) ≫
      ((Sheaf.restrictScalars (ProEt.topology W)
        (finiteDualizingQuotient l E h)).mapDerivedCategorySingleFunctor 0).inv.app (𝟙_ _))
    (fixedCoordinates l E W m).hom (fixedCoordinates l E W n).hom
    (((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
      (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
    ((DerivedCategory.singleFunctor _ 0).map q)
    (by
      simp only [Category.assoc]
      exact hs) hd

set_option maxHeartbeats 4000000 in
-- The comparison transports both the small and standard derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
/-- The specified finite scalar-adjunction quotient becomes the actual regular-module
quotient in the explicit finite realization coordinates.
Source: blueprint finite mapping-complex comparison, proof paragraph 2.
(blueprint: new-lem-coef-integral-unit-finite-quotient-coordinates).
Proof: quotient-diagram naturality identifies the normalized DVR ring map with its
generic intrinsic scalar map. Apply the proved intrinsic unit square to q and its
normalization on 1, and the proved comparison-site scalar-adjunct square. Normalize
the site and intrinsic unit coordinates using the identity single/unit comparisons.
Naturality of the intrinsic comparison pastes the two squares. Unfold the specified
realization restriction composite to identify the outer arrow with the finite quotient.
The proof works for every n ≤ m, including equal levels and n = 0. -/
theorem integralDualizingFiniteUnitQuotient_coordinates {m n : ℕ} (h : n ≤ m)
    (q : SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (normalizedDVRModuleRes l E W h).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
    (hq : ∀ U : W.ProEtᵒᵖ, q.val.app U
      (1 : (integralCoefficientSheaf l E W m).obj.obj U) =
        (1 : (integralCoefficientSheaf l E W n).obj.obj U)) :
    let cm :=
      (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (m + 1))).functor.mapIso
          (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
            (finiteDualizingCoeff l E m) W) ≪≫
              finiteDualizingIntrinsicUnit l E W m
    let cn :=
      (sfIntrinsicDerivedEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
          (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
            (finiteDualizingCoeff l E n) W) ≪≫
              finiteDualizingIntrinsicUnit l E W n
    integralDualizingFiniteUnitQuotient l E W h ≫
      (normalizedDVRRes l E W h).map cn.hom ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    cm.hom ≫
      (DerivedCategory.singleFunctor _ 0).map q := by
  change
    integralDualizingFiniteUnitQuotient l E W h ≫
      (normalizedDVRRes l E W h).map (unitCoordinates l E W n).hom ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    (unitCoordinates l E W m).hom ≫
      (DerivedCategory.singleFunctor _ 0).map q
  exact coordinates_of_paste (normalizedDVRRes l E W h)
    (finite_unit_quotient_form l E W h)
    (unitCoordinates_hom l E W m) (unitCoordinates_hom l E W n)
    (pasted_unit_square l E W h q hq)

end WeilConjectures
