/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralDualizingSystemUnitComparison
public import WeilConjectures.SixFunctors.IntegralDualizingFiniteUnitQuotient
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

import WeilConjectures.SixFunctors.IntegralDualizingFiniteUnitCoordinates

/-! # The quotient transition on the coefficient system unit -/

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

private theorem localized_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) (M : C) :
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) _ _ F.mapDerivedCategory G.mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)).app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app M =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map (a.app M) := by
  change (Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) _ _ F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)).app
      (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫ _ = _
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq,
    Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  erw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 1
  rw [← DerivedCategory.Q.map_comp]
  change _ = _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  ext i
  by_cases hi : i = 0
  · subst i
    have h' : a.app (((HomologicalComplex.single C (.up ℤ) 0).obj M).X 0) =
        F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ a.app M ≫
          G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv := by
      rw [a.naturality_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, h', HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom,
      Iso.refl_inv, Category.id_comp,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X',
      HomologicalComplex.single_map_f_self]
    erw [G.map_id, Category.comp_id, Category.id_comp, Category.comp_id]
    erw [F.map_id, Category.id_comp, Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

private theorem transition_single (M : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W h).app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (normalizedDVRRes l E W h).map
        (((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        ((coefficientSequenceEvaluation l E W n).obj M) =
    ((coefficientSequenceEvaluation l E W m).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((coefficientSequenceTransition l E W h).app M) := by
  dsimp only [coefficientSequenceDerivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  exact localized_single _ _ (coefficientSequenceTransition l E W h) M

private theorem pushforwardUnit_inv_one
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    {S : Sheaf J RingCat.{u + 1}}
    (h : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R = S)
    (U : Cᵒᵖ) :
    (integralDualizingPushforwardUnitIso F R h).inv.val.app U
        (1 : S.obj.obj U) = (1 : R.obj.obj (F.op.obj U)) := by
  subst S
  rfl

private abbrev sequenceUnit :=
  SheafOfModules.unit
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E W))

private def regularQuotient {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (normalizedDVRModuleRes l E W h).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) :=
  restriction_unit_map (normalizedDVRQuotient l E W h)

set_option maxHeartbeats 2000000 in
-- Compute the ordinary evaluated transition on its regular generator.
private theorem ordinary_transition {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceTransition l E W h).app (sequenceUnit l E W) ≫
      (normalizedDVRModuleRes l E W h).map
        (integralDualizingOrdinaryUnitEvaluation l E W n).hom =
    (integralDualizingOrdinaryUnitEvaluation l E W m).hom ≫
      regularQuotient l E W h := by
  apply (cancel_epi (integralDualizingOrdinaryUnitEvaluation l E W m).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext U
  have hi := pushforwardUnit_inv_one (Prod.sectR m W.ProEt) _
    (coefficientSequenceEvaluationRing_eq l E W m) U
  change (integralDualizingOrdinaryUnitEvaluation l E W m).inv.val.app U
    (1 : (integralCoefficientSheaf l E W m).obj.obj U) = _ at hi
  have ht := (coefficientSequenceTransition_exists l E W h).exists.choose_spec
    (sequenceUnit l E W) U
  have hx := congrArg (fun f ↦ f (1 :
    (coefficientSequenceCommRingSheaf l E W).obj.obj (op (m, U.unop)))) ht
  change ((coefficientSequenceTransition l E W h).app (sequenceUnit l E W)).val.app U
    (1 : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (m, U.unop))) = _ at hx
  have ht1 := hx.trans (PresheafOfModules.unit_map_one
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E W)).obj
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  have hn := pushforwardUnit_inv_one (Prod.sectR n W.ProEt) _
    (coefficientSequenceEvaluationRing_eq l E W n) U
  change (integralDualizingOrdinaryUnitEvaluation l E W n).inv.val.app U
    (1 : (integralCoefficientSheaf l E W n).obj.obj U) = _ at hn
  have hni := congrArg
    (fun f : SheafOfModules.unit (integralCoefficientSheaf l E W n) ⟶
        SheafOfModules.unit (integralCoefficientSheaf l E W n) ↦
      f.val.app U (1 : (integralCoefficientSheaf l E W n).obj.obj U))
    (integralDualizingOrdinaryUnitEvaluation l E W n).inv_hom_id
  change (integralDualizingOrdinaryUnitEvaluation l E W n).hom.val.app U
    (((coefficientSequenceTransition l E W h).app (sequenceUnit l E W)).val.app U
      ((integralDualizingOrdinaryUnitEvaluation l E W m).inv.val.app U
        (1 : (integralCoefficientSheaf l E W m).obj.obj U))) = _
  erw [hi, ht1]
  change (integralDualizingOrdinaryUnitEvaluation l E W n).hom.val.app U
    (1 : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, U.unop))) =
    (normalizedDVRQuotient l E W h).hom.app U
      (1 : (integralCoefficientSheaf l E W m).obj.obj U)
  rw [((normalizedDVRQuotient l E W h).hom.app U).hom.map_one]
  change (integralDualizingOrdinaryUnitEvaluation l E W n).hom.val.app U
    ((integralDualizingOrdinaryUnitEvaluation l E W n).inv.val.app U
      (1 : (integralCoefficientSheaf l E W n).obj.obj U)) = _ at hni
  erw [hn] at hni
  exact hni

-- Keep exact derived models fixed while normalizing comparison coordinates.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] coefficientSequenceHasDerived scalarReductionTargetDerived
  finiteDualizingRealization

attribute [local implicit_reducible] Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  sfIntrinsicDerivedEquivalence integralCoefficientSheaf Etale.constantComplex
  SheafOfModules.unit PresheafOfModules.unit ExistsUnique ProEtale.pbcFixedScalarExtension
  reductionModulesHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
set_option maxHeartbeats 4000000 in
-- The comparison transports both the small and standard derived models.
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem finite_quotient_coordinates {m n : ℕ} (h : n ≤ m) :
    integralDualizingFiniteUnitQuotient l E W h ≫
      (normalizedDVRRes l E W h).map (unitCoordinates l E W n).hom ≫
      ((normalizedDVRModuleRes l E W h).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) =
    (unitCoordinates l E W m).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (regularQuotient l E W h) := by
  exact integralDualizingFiniteUnitQuotient_coordinates l E W h (regularQuotient l E W h)
    (fun U ↦ ((normalizedDVRQuotient l E W h).hom.app U).hom.map_one)

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem evaluation_coordinates (n : ℕ) :
    (integralDualizingRegularUnitEvaluation l E W n).hom ≫
      (unitCoordinates l E W n).hom =
    ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).hom.app
        (sequenceUnit l E W) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (integralDualizingOrdinaryUnitEvaluation l E W n).hom := by
  dsimp only [integralDualizingRegularUnitEvaluation, unitCoordinates, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem transition_coordinates
    {S A B : Type*} [Category S] [Category A] [Category B]
    [Abelian S] [Abelian A] [Abelian B]
    [dcS : HasDerivedCategory S] [dcA : HasDerivedCategory A]
    [dcB : HasDerivedCategory B]
    (F : S ⥤ A) (G : S ⥤ B) (R : B ⥤ A)
    [F.Additive] [G.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (τ : F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (t : F ⟶ G ⋙ R) (M : S) (N : A) (P : B)
    (a : F.obj M ≅ N) (b : G.obj M ≅ P)
    {U : DerivedCategory A} {V : DerivedCategory B}
    (u : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor S 0).obj M) ≅ U)
    (v : G.mapDerivedCategory.obj ((DerivedCategory.singleFunctor S 0).obj M) ≅ V)
    (c : U ≅ (DerivedCategory.singleFunctor A 0).obj N)
    (d : V ≅ (DerivedCategory.singleFunctor B 0).obj P)
    (q : U ⟶ R.mapDerivedCategory.obj V) (r : N ⟶ R.obj P)
    (ht : τ.app ((DerivedCategory.singleFunctor S 0).obj M) ≫
        R.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (R.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor A 0).map (t.app M))
    (ho : t.app M ≫ R.map b.hom = a.hom ≫ r)
    (hu : u.hom ≫ c.hom = (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor A 0).map a.hom)
    (hv : v.hom ≫ d.hom = (G.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor B 0).map b.hom)
    (hq : q ≫ R.mapDerivedCategory.map d.hom ≫
        (R.mapDerivedCategorySingleFunctor 0).hom.app P =
      c.hom ≫ (DerivedCategory.singleFunctor A 0).map r) :
    τ.app ((DerivedCategory.singleFunctor S 0).obj M) ≫
      R.mapDerivedCategory.map v.hom = u.hom ≫ q := by
  apply (cancel_mono (R.mapDerivedCategory.map d.hom ≫
    (R.mapDerivedCategorySingleFunctor 0).hom.app P)).mp
  simp only [Category.assoc]
  rw [hq, ← R.mapDerivedCategory.map_comp_assoc, hv, R.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  have hn := (R.mapDerivedCategorySingleFunctor 0).hom.naturality b.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [reassoc_of% ht]
  rw [← (DerivedCategory.singleFunctor A 0).map_comp, ho]
  rw [← Category.assoc, hu]
  simp only [Functor.map_comp, Category.assoc]

set_option maxHeartbeats 4000000 in
-- The comparison coordinates contain several exact derived functors.
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
/-- The regular coefficient system has the genuine quotient maps in the normalized
finite etale unit coordinates.
Source: Stacks 07A4 and 0941; finite counit compatibility, proof step 2.
(blueprint: lem-coef-finite-unit-quotient).
Proof: coefficientSequenceTransition is the horizontal restriction of the module
presheaf. On its regular module this is the coefficient sheaf quotient. Evaluate the
single complex and use the canonical exact-functor single comparison to identify the
derived transition with that quotient in degree zero. The scalar-adjunction unit on
the etale regular unit sends a to 1 tensor a; the normalized scalar-unit comparison
sends this to the quotient of a. Comparison pullback preserves these generators.
The generator-normalized finiteDualizingIntrinsicUnit and section-normalized
finiteDualizingRealizationRestriction therefore carry the same quotient map to the
intrinsic regular module. Equality on local constant scalar generators gives equality
of sheaf maps, and exact localization gives the displayed equality. The argument
applies to every scheme W, to equal levels, and at the first quotient. -/
theorem integralDualizingRegularUnit_transition {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W h).app
        ((DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
          (SheafOfModules.unit
            ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (coefficientSequenceCommRingSheaf l E W)))) ≫
      (normalizedDVRRes l E W h).map
        (integralDualizingRegularUnitEvaluation l E W n).hom =
    (integralDualizingRegularUnitEvaluation l E W m).hom ≫
      integralDualizingFiniteUnitQuotient l E W h := by
  exact transition_coordinates
    (dcS := HasDerivedCategory.standard _) (dcA := HasDerivedCategory.standard _)
    (dcB := HasDerivedCategory.standard _)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (normalizedDVRModuleRes l E W h) (coefficientSequenceDerivedTransition l E W h)
    (coefficientSequenceTransition l E W h) (sequenceUnit l E W)
    (SheafOfModules.unit (integralCoefficientSheaf l E W m))
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (integralDualizingOrdinaryUnitEvaluation l E W m)
    (integralDualizingOrdinaryUnitEvaluation l E W n)
    (integralDualizingRegularUnitEvaluation l E W m)
    (integralDualizingRegularUnitEvaluation l E W n)
    (unitCoordinates l E W m) (unitCoordinates l E W n)
    (integralDualizingFiniteUnitQuotient l E W h) (regularQuotient l E W h)
    (transition_single l E W (sequenceUnit l E W) h) (ordinary_transition l E W h)
    (evaluation_coordinates l E W m) (evaluation_coordinates l E W n)
    (finite_quotient_coordinates l E W h)

end WeilConjectures
