/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import all Mathlib.Logic.Small.Defs

/-! # Basic comparison for supported Hom classes

The three comparison bijections and the two coefficient-source squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupSingle functorialCupSourceObject functorialCupTarget
  functorialCupConstant functorialCupComparisonFunctor constant constantEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

private theorem exactHom_bijective {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S T : B) (a : ℤ)
    (h : Function.Bijective (F.mapDerivedCategory.map
      (X := (DerivedCategory.singleFunctor B 0).obj S)
      (Y := ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧))) :
    Function.Bijective (functorialCupExactHom F (S := S) (T := T) a) := by
  let eS := (F.mapDerivedCategorySingleFunctor 0).app S
  let eT := (F.mapDerivedCategory.commShiftIso a).app
      ((DerivedCategory.singleFunctor B 0).obj T) ≪≫
    (shiftFunctor (DerivedCategory D) a).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app T)
  have he := eT.homToEquiv.bijective.comp (eS.homFromEquiv.bijective.comp h)
  dsimp only [Functor.comp_obj] at he
  change Function.Bijective (fun α ↦ eS.inv ≫ F.mapDerivedCategory.map α ≫ eT.hom)
  simpa only [Function.comp_def, Iso.homToEquiv_apply, Iso.homFromEquiv_apply,
    Category.assoc] using he

private theorem normalizedHom_bijective {B D : Type c}
    [Category.{v} B] [Category.{v} D] [Abelian B] [Abelian D]
    [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : B} {S' T' : D} (eS : F.obj S ≅ S') (eT : F.obj T ≅ T') (a : ℤ)
    (h : Function.Bijective (functorialCupExactHom F (S := S) (T := T) a)) :
    Function.Bijective (functorialCupNormalizedHom F eS eT a) := by
  let E := DerivedCategory.singleFunctor D 0
  let eSource := E.mapIso eS
  let eTarget := (shiftFunctor (DerivedCategory D) a).mapIso (E.mapIso eT)
  have he := eTarget.homToEquiv.bijective.comp (eSource.homFromEquiv.bijective.comp h)
  change Function.Bijective (fun α ↦ E.map eS.inv ≫ functorialCupExactHom F a α ≫
    (E.map eT.hom)⟦a⟧')
  simpa only [Function.comp_def, Iso.homToEquiv_apply, Iso.homFromEquiv_apply,
    Functor.mapIso_inv, Functor.mapIso_hom,
    eSource, eTarget, E, Category.assoc] using he

private theorem comparison_exactHom_bijective (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (S T : P.functorialCupSheaves false X) (a : ℤ) :
    Function.Bijective (functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X)
      (S := S) (T := T) a) := by
  apply exactHom_bijective
  exact ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    ((P.functorialCupSingle false X).obj S)
    (((P.functorialCupSingle false X).obj T)⟦a⟧) (by
      exact ⟨-a, DerivedCategory.TStructure.t.isGE_shift _ 0 a (-a)⟩)

private theorem comparison_supported_bijective (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonSupportedBijective := by
  unfold FunctorialCupComparisonSupportedBijective
  intro C X i hi aX a r
  change Function.Bijective (functorialCupNormalizedHom
    (hB := P.functorialCupHasDerived false X) (hD := P.functorialCupHasDerived true X)
    (P.functorialCupComparisonFunctor X) (P.functorialCupComparisonSource_existsUnique i).choose
    (eqToIso (P.functorialCupComparisonTwist_eq X r)) a)
  exact normalizedHom_bijective _ _ _ a (comparison_exactHom_bijective P X _ _ a)

private theorem comparison_ordinary_bijective (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonOrdinaryBijective := by
  unfold FunctorialCupComparisonOrdinaryBijective
  intro X aX a r
  change Function.Bijective (functorialCupNormalizedHom
    (hB := P.functorialCupHasDerived false X) (hD := P.functorialCupHasDerived true X)
    (P.functorialCupComparisonFunctor X) (eqToIso (P.functorialCupComparisonConstant_eq X))
    (eqToIso (P.functorialCupComparisonTwist_eq X r)) a)
  exact normalizedHom_bijective _ _ _ a (comparison_exactHom_bijective P X _ _ a)

private theorem comparison_open_bijective (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonOpenBijective := by
  unfold FunctorialCupComparisonOpenBijective
  intro C X i hi aX a r
  change Function.Bijective (functorialCupNormalizedHom
    (hB := P.functorialCupHasDerived false X) (hD := P.functorialCupHasDerived true X)
    (P.functorialCupComparisonFunctor X) (P.functorialCupComparisonOpen_existsUnique i).choose
    (eqToIso (P.functorialCupComparisonTwist_eq X r)) a)
  exact normalizedHom_bijective _ _ _ a (comparison_exactHom_bijective P X _ _ a)

private theorem exactHom_pre {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S S' T : B} (f : S' ⟶ S) (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧) :
    functorialCupExactHom F a ((DerivedCategory.singleFunctor B 0).map f ≫ α) =
      (DerivedCategory.singleFunctor D 0).map (F.map f) ≫ functorialCupExactHom F a α := by
  simp only [functorialCupExactHom, Functor.map_comp, Category.assoc]
  have h := (F.mapDerivedCategorySingleFunctor 0).inv.naturality f
  dsimp only [Functor.comp_map] at h
  rw [← reassoc_of% h]

private theorem exactHom_source_square {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T M : B} {S' T' : D} (f : S ⟶ T) (f' : S' ⟶ T')
    (eS : F.obj S ≅ S') (eT : F.obj T ≅ T')
    (h : F.map f ≫ eT.hom = eS.hom ≫ f') (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj T ⟶
      ((DerivedCategory.singleFunctor B 0).obj M)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).map f' ≫
        (DerivedCategory.singleFunctor D 0).map eT.inv ≫ functorialCupExactHom F a α =
      (DerivedCategory.singleFunctor D 0).map eS.inv ≫
        functorialCupExactHom F a ((DerivedCategory.singleFunctor B 0).map f ≫ α) := by
  have he : f' ≫ eT.inv = eS.inv ≫ F.map f := by
    apply (cancel_mono eT.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  rw [exactHom_pre]
  simp only [← Functor.map_comp_assoc, he]

private theorem normalized_source_square
    {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T U : B} {S' T' U' : D} (f : S ⟶ T) (f' : S' ⟶ T')
    (eS : F.obj S ≅ S') (eT : F.obj T ≅ T') (eU : F.obj U ≅ U')
    (h : F.map f ≫ eT.hom = eS.hom ≫ f') (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj T ⟶
      ((DerivedCategory.singleFunctor B 0).obj U)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).map f' ≫
        functorialCupNormalizedHom F eT eU a α =
      functorialCupNormalizedHom F eS eU a
        ((DerivedCategory.singleFunctor B 0).map f ≫ α) := by
  simpa only [functorialCupNormalizedHom, Category.assoc] using
    congrArg (fun k ↦ k ≫ ((DerivedCategory.singleFunctor D 0).map eU.hom)⟦a⟧')
      (exactHom_source_square F f f' eS eT h a α)

private theorem comparison_forget (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonForgetSupport := by
  unfold FunctorialCupComparisonForgetSupport
  intro C X i hi a r α
  have h := normalized_source_square
    (hB := P.functorialCupHasDerived false X) (hD := P.functorialCupHasDerived true X)
    (P.functorialCupComparisonFunctor X)
    (P.functorialCupRestriction false i) (P.functorialCupRestriction true i)
    (eqToIso (P.functorialCupComparisonConstant_eq X))
    (P.functorialCupComparisonSource_existsUnique i).choose
    (eqToIso (P.functorialCupComparisonTwist_eq X r))
    (by
      change _ = 𝟙 _ ≫ _
      simpa only [Category.id_comp] using
        (P.functorialCupComparisonSource_existsUnique i).choose_spec.1) a α
  exact h.symm

private theorem comparison_open (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonOpenRestriction := by
  unfold FunctorialCupComparisonOpenRestriction
  intro C X i hi a r α
  have h := normalized_source_square
    (hB := P.functorialCupHasDerived false X) (hD := P.functorialCupHasDerived true X)
    (P.functorialCupComparisonFunctor X)
    (P.functorialCupOpenInclusion false i) (P.functorialCupOpenInclusion true i)
    (P.functorialCupComparisonOpen_existsUnique i).choose
    (eqToIso (P.functorialCupComparisonConstant_eq X))
    (eqToIso (P.functorialCupComparisonTwist_eq X r))
    (by
      change _ ≫ 𝟙 _ = _
      simpa only [Category.comp_id] using
        (P.functorialCupComparisonOpen_existsUnique i).choose_spec.1) a α
  exact h.symm

/-- The three comparison bijections and the two source-arrow squares.
Source: exact finite-coefficient site comparison and Stacks 09XP
(blueprint: lem-pur-supported-cup-comparison-basic).
Proof: conjugate the fully faithful exact comparison Hom map by the normalized
single and shift isomorphisms. The defining source and open normalization squares
then give compatibility of precomposition with restriction and inclusion. -/
theorem supportedCupComparisonBasic (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonSupportedBijective ∧ P.FunctorialCupComparisonOrdinaryBijective ∧
      P.FunctorialCupComparisonOpenBijective ∧ P.FunctorialCupComparisonForgetSupport ∧
      P.FunctorialCupComparisonOpenRestriction := by
  exact ⟨comparison_supported_bijective P, comparison_ordinary_bijective P,
    comparison_open_bijective P, comparison_forget P, comparison_open P⟩

end WeilConjectures.PurityFiniteSetting
