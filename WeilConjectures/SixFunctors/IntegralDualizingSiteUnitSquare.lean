/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
import WeilConjectures.AlgebraicGeometry.ScalarUnitRestrictionSingle
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # The site regular-unit restriction square -/

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

private def siteCoordinates (A : Type (u + 1)) [CommRing A] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory.mapIso
      (Etale.constantComplexIsoSingleFunctor A W) ≪≫
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategorySingleFunctor
      0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (ProEtale.comparisonUpperStarUnitIso A W)

private theorem site_restriction_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars W.smallEtaleTopology φ)) ≫
      (ProEtale.pbcComparisonRestrict W φ).inv.app (𝟙_ _) ≫
      (Sheaf.restrictScalars (ProEt.topology W) φ).map
        (ProEtale.comparisonUpperStarUnitIso B W).hom =
    (ProEtale.comparisonUpperStarUnitIso A W).hom ≫
      Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W) φ) := by
  let a := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) W
  let b := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) W
  let LA := ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) W
  let LB := ProEtale.comparisonLowerStar (ModuleCat.{u + 1} B) W
  let U := Sheaf.restrictScalars W.smallEtaleTopology φ
  let V := Sheaf.restrictScalars (ProEt.topology W) φ
  let ε := Functor.LaxMonoidal.ε U
  have h := unit_mateEquiv b a
    (TwoSquare.mk _ _ _ _ (ProEtale.pbcComparisonRestrict W φ).inv) (𝟙_ _)
  have hm := congr_app (ProEtale.comparison_restrict_mate W φ)
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W).obj (𝟙_ _))
  dsimp only [TwoSquare.natTrans] at hm
  rw [hm] at h
  have hc : a.unit.app (U.obj (𝟙_ _)) ≫
      LA.map ((ProEtale.pbcComparisonRestrict W φ).inv.app (𝟙_ _)) =
      U.map (b.unit.app (𝟙_ _)) := by
    exact h.symm.trans (Category.comp_id _)
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  erw [← a.unit.naturality_assoc ε]
  erw [reassoc_of% hc]
  change ε ≫ U.map (b.unit.app (𝟙_ _)) ≫
    U.map (LB.map (ProEtale.comparisonUpperStarUnitIso B W).hom) = _
  rw [← U.map_comp]
  have hb : b.unit.app (𝟙_ _) ≫ LB.map
      (ProEtale.comparisonUpperStarUnitIso B W).hom =
      Functor.LaxMonoidal.ε LB := by
    exact b.unit_app_unit_comp_map_η
  have ha : a.unit.app (𝟙_ _) ≫ LA.map
      (ProEtale.comparisonUpperStarUnitIso A W).hom =
      Functor.LaxMonoidal.ε LA := by
    exact a.unit_app_unit_comp_map_η
  rw [hb, ← Category.assoc, ha]
  have hu := NatTrans.IsMonoidal.unit
    (τ := (Functor.sheafPushforwardContinuousCompSheafComposeIso (toProEt W)
      W.smallEtaleTopology (ProEt.topology W) (ModuleCat.restrictScalars.{u + 1} φ)).hom)
  simpa only [ε, U, V, LA, LB, ProEtale.comparisonLowerStar,
    ProEtale.laxMonoidal_comparisonLowerStar, Sheaf.restrictScalars,
    Functor.LaxMonoidal.comp_ε, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using hu

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

private theorem exact_square_transport
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
    (ho : F.map f ≫ e.inv.app N ≫ V.map b.hom = a.hom ≫ q)
    {X : DerivedCategory A} {Y : DerivedCategory B}
    (i : X ≅ (DerivedCategory.singleFunctor A 0).obj M)
    (j : Y ≅ (DerivedCategory.singleFunctor B 0).obj N)
    (t : X ⟶ U.mapDerivedCategory.obj Y)
    (ht : t ≫ U.mapDerivedCategory.map j.hom =
      i.hom ≫ (DerivedCategory.singleFunctor A 0).map f ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N) :
    F.mapDerivedCategory.map t ≫
      (Functor.mapDerivedCategorySquareIso e).inv.app Y ≫
      V.mapDerivedCategory.map (G.mapDerivedCategory.map j.hom ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor D 0).map b.hom) =
    (F.mapDerivedCategory.map i.hom ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map a.hom) ≫
      (DerivedCategory.singleFunctor C 0).map q ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app Q := by
  have hd := exact_square_regular_inv F G U V e a b f q ho
  simp only [Functor.map_comp, Category.assoc] at hd
  apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app Q)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [← reassoc_of% ((Functor.mapDerivedCategorySquareIso e).inv.naturality j.hom)]
  rw [← F.mapDerivedCategory.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ F.mapDerivedCategory.map i.hom ≫ k) hd

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

set_option maxHeartbeats 4000000 in
-- The comparison transports both the small and standard derived models.
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
/-- In exact single-complex coordinates, the site comparison carries the finite
etale scalar adjunct on the regular unit to the ordinary scalar restriction unit.
Source: blueprint finite mapping-complex comparison, proof paragraph 2.
(blueprint: new-lem-coef-integral-unit-site-square).
Proof: transpose the comparison square through the comparison adjunction. The
lower-star restriction interchange is monoidal, so its lax unit square commutes.
Transpose back to get the ordinary upper-star unit square. The existing normalized
scalar-unit restriction formula identifies the scalar adjunct in single coordinates.
Apply exact-square/single coherence and naturality to obtain the displayed equality.
The argument uses arbitrary coefficient rings and covers identity ring maps. -/
theorem integralDualizingSiteUnit_restriction_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    let ca :=
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory.mapIso
        (Etale.constantComplexIsoSingleFunctor A W) ≪≫
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            W).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (ProEtale.comparisonUpperStarUnitIso A W)
    let cb :=
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W).mapDerivedCategory.mapIso
        (Etale.constantComplexIsoSingleFunctor B W) ≪≫
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B)
            W).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (ProEtale.comparisonUpperStarUnitIso B W)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).homEquiv _ _
            (Etale.ExceptionalCoefficients.unitIso φ W).hom) ≫
      (ProEtale.pbcDerivedComparisonRestrict W φ).inv.app (Etale.constantComplex B W) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology W) φ).map
        cb.hom =
    ca.hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W) φ)) ≫
      ((Sheaf.restrictScalars (ProEt.topology W) φ).mapDerivedCategorySingleFunctor 0).inv.app
        (𝟙_ _) := by
  change
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).homEquiv _ _
            (Etale.ExceptionalCoefficients.unitIso φ W).hom) ≫
      (ProEtale.pbcDerivedComparisonRestrict W φ).inv.app (Etale.constantComplex B W) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology W) φ).map
        (siteCoordinates W B).hom =
    (siteCoordinates W A).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars (ProEt.topology W) φ)) ≫
      ((Sheaf.restrictScalars (ProEt.topology W) φ).mapDerivedCategorySingleFunctor 0).inv.app
        (𝟙_ _)
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W
  let G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W
  let U := Sheaf.restrictScalars W.smallEtaleTopology φ
  let V := Sheaf.restrictScalars (ProEt.topology W) φ
  let iA := Etale.constantComplexIsoSingleFunctor A W
  let iB := Etale.constantComplexIsoSingleFunctor B W
  let t := (Adjunction.ofIsRightAdjoint U.mapDerivedCategory).homEquiv _ _
    (Etale.ExceptionalCoefficients.unitIso φ W).hom
  have hs : t ≫ U.mapDerivedCategory.map iB.hom =
      iA.hom ≫ (DerivedCategory.singleFunctor _ 0).map (Functor.LaxMonoidal.ε U) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app (𝟙_ _) := by
    apply (cancel_mono ((U.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simpa only [t, U, iA, iB, Etale.constantComplex, Sheaf.derivedRestrictScalars,
      Adjunction.homEquiv_unit,
      Functor.map_comp, Category.assoc] using
      Etale.scalarUnit_restriction_single φ W
  have hd := exact_square_transport F G U V (ProEtale.pbcComparisonRestrict W φ)
    (ProEtale.comparisonUpperStarUnitIso A W) (ProEtale.comparisonUpperStarUnitIso B W)
    (Functor.LaxMonoidal.ε U) (Functor.LaxMonoidal.ε V) (site_restriction_unit W φ)
    iA iB t hs
  simpa only [siteCoordinates, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ProEtale.pbcDerivedComparisonRestrict, Functor.mapDerivedCategorySquareIso,
    Sheaf.derivedRestrictScalars, Functor.map_comp, Category.assoc] using hd


end WeilConjectures
