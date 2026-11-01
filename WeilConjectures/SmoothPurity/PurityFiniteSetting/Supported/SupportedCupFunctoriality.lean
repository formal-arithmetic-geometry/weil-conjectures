/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupAlgebra
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupComparison

/-! # Localization part of supported cup functoriality

The actual closed/open coefficient sequence is functorial under exact inverse image.
The independent cup algebra and comparison results supply the remaining clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] catToReflQuiver functorialCupSingle
  functorialCupSourceObject functorialCupTarget

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupConstant functorialCupRestriction
  functorialCupFullSupportIso constant constantEtale functorialCupComparisonFunctor

set_option backward.isDefEq.respectTransparency false in

private theorem shifted_conjugate_comp {D : Type c} [Category.{v} D] [HasShift D ℤ]
    {X Y Z X' Y' Z' : D} (eX : X' ≅ X) (eY : Y' ≅ Y) (eZ : Z' ≅ Z)
    {a b c : ℤ} (h : b + a = c) (f : X ⟶ Y⟦a⟧) (g : Y ⟶ Z⟦b⟧) :
    ShiftedHom.comp (eX.hom ≫ f ≫ eY.inv⟦a⟧')
        (eY.hom ≫ g ≫ eZ.inv⟦b⟧') h =
      eX.hom ≫ ShiftedHom.comp f g h ≫ eZ.inv⟦c⟧' := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← (shiftFunctor D a).map_comp_assoc eY.inv eY.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun k => eX.hom ≫ f ≫ (shiftFunctor D a).map g ≫ k)
    ((shiftFunctorAdd' D b a c h).inv.naturality eZ.inv)

private theorem exactHom_comp {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T M : B} {a b c : ℤ} (h : b + a = c)
    (f : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧)
    (g : (DerivedCategory.singleFunctor B 0).obj T ⟶
      ((DerivedCategory.singleFunctor B 0).obj M)⟦b⟧) :
    functorialCupExactHom F c (ShiftedHom.comp f g h) =
      ShiftedHom.comp (functorialCupExactHom F a f) (functorialCupExactHom F b g) h := by
  have hcomp := shifted_conjugate_comp
    ((F.mapDerivedCategorySingleFunctor 0).app S).symm
    ((F.mapDerivedCategorySingleFunctor 0).app T).symm
    ((F.mapDerivedCategorySingleFunctor 0).app M).symm h
    (ShiftedHom.map f F.mapDerivedCategory) (ShiftedHom.map g F.mapDerivedCategory)
  rw [← ShiftedHom.map_comp] at hcomp
  simpa only [functorialCupExactHom, ShiftedHom.map, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc] using hcomp.symm

private theorem exactHom_singleδ {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex B} (hS : S.ShortExact) :
    functorialCupExactHom F 1 hS.singleδ = (hS.map_of_exact F).singleδ := by
  simpa only [functorialCupExactHom, ShiftedHom.map, Category.assoc] using
    hS.mapShiftedHom_singleδ' F

private theorem exactHom_boundary_square {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex B} {T : ShortComplex D} (hS : S.ShortExact) (hT : T.ShortExact)
    (e : S.map F ≅ T) {M : B} {M' : D} (eM : F.obj M ≅ M') (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S.X₁ ⟶
      ((DerivedCategory.singleFunctor B 0).obj M)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).map (ShortComplex.π₃.mapIso e).inv ≫
        functorialCupExactHom F (a + 1) (ShiftedHom.comp hS.singleδ α rfl) ≫
        ((DerivedCategory.singleFunctor D 0).map eM.hom)⟦a + 1⟧' =
      ShiftedHom.comp hT.singleδ
        ((DerivedCategory.singleFunctor D 0).map (ShortComplex.π₁.mapIso e).inv ≫
          functorialCupExactHom F a α ≫
          ((DerivedCategory.singleFunctor D 0).map eM.hom)⟦a⟧') rfl := by
  let E := DerivedCategory.singleFunctor D 0
  let e₁ := E.mapIso (ShortComplex.π₁.mapIso e)
  let e₃ := E.mapIso (ShortComplex.π₃.mapIso e)
  have hd : e₃.inv ≫ functorialCupExactHom F 1 hS.singleδ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      hT.singleδ := by
    rw [exactHom_singleδ]
    have h := (ShortComplex.ShortExact.singleTriangle.map (hS.map_of_exact F) hT e.hom).comm₃
    change (hS.map_of_exact F).singleδ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ hT.singleδ at h
    have hh := congrArg (fun k => e₃.inv ≫ k) h
    dsimp [e₁, e₃, E] at hh ⊢
    simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      ← CategoryTheory.Functor.map_comp, ← ShortComplex.comp_τ₃,
      Iso.inv_hom_id, ShortComplex.id_τ₃, CategoryTheory.Functor.map_id,
      Category.id_comp] using hh
  rw [exactHom_comp]
  have hc := shifted_conjugate_comp e₃.symm e₁.symm (E.mapIso eM).symm
    (a := 1) (b := a) (c := a + 1) rfl
    (functorialCupExactHom F 1 hS.singleδ) (functorialCupExactHom F a α)
  simp only [Iso.symm_hom, Iso.symm_inv] at hc
  dsimp [e₁, e₃, E, ShortComplex.π₁, ShortComplex.π₃] at hd hc
  rw [hd] at hc
  simpa only [e₃, e₁, E, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.symm_hom, Iso.symm_inv, ShortComplex.π₁, ShortComplex.π₃,
    Category.assoc] using hc.symm

private theorem normalized_boundary_square {B D : Type c}
    [Category.{v} B] [Category.{v} D] [Abelian B] [Abelian D]
    [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex B} {T : ShortComplex D} (hS : S.ShortExact) (hT : T.ShortExact)
    (e₁ : F.obj S.X₁ ≅ T.X₁) (e₂ : F.obj S.X₂ ≅ T.X₂) (e₃ : F.obj S.X₃ ≅ T.X₃)
    (hf : F.map S.f ≫ e₂.hom = e₁.hom ≫ T.f)
    (hg : F.map S.g ≫ e₃.hom = e₂.hom ≫ T.g)
    {M : B} {M' : D} (eM : F.obj M ≅ M') (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S.X₁ ⟶
      ((DerivedCategory.singleFunctor B 0).obj M)⟦a⟧) :
    functorialCupNormalizedHom F e₃ eM (a + 1) (ShiftedHom.comp hS.singleδ α rfl) =
      ShiftedHom.comp hT.singleδ (functorialCupNormalizedHom F e₁ eM a α) rfl := by
  let e : S.map F ≅ T := ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm
  have h := exactHom_boundary_square F hS hT e eM a α
  simpa only [functorialCupNormalizedHom, ShortComplex.π₁, ShortComplex.π₃,
    Functor.mapIso_inv, ShortComplex.isoMk, ShortComplex.homMk, e, Category.assoc] using h

private theorem restriction_full (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupRestriction pro (𝟙 X) = (P.functorialCupFullSupportIso pro X).inv := by
  cases pro with
  | false =>
    change Etale.closedConstantSectionMap P.Coefficient (𝟙 X) = _
    unfold Etale.closedConstantSectionMap
    rw [(Etale.constantModulePushforwardMap_id_comp P.Coefficient
      (ModuleCat.of P.Coefficient P.Coefficient)).1]
    erw [Category.comp_id]
    rfl
  | true =>
    let : HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
      P.functorialCupTopologySheafify true X
    let : HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
      HasSheafify.isRightAdjoint
    let := Scheme.ProEt.isContinuous_overPullback (𝟙 X)
    change ProEtale.cupCoefficientRestriction P (𝟙 X) = _
    have h : ProEtale.cupCoefficientRestriction P (𝟙 X) =
        (ProEtale.cupConstantIso P X).hom ≫
          Functor.LaxMonoidal.ε
            (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)) ≫
          (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)).map
            (ProEtale.cupConstantIso P X).inv := by
      unfold ProEtale.cupCoefficientRestriction
      congr 1
      congr 1
      apply ((constantSheafAdj (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝟙 X))
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
        (Scheme.ProEt.topology X) (op (Scheme.ProEt.mk (𝟙 X)))).symm
    rw [h]
    have hε : Functor.LaxMonoidal.ε
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)) =
        (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app (𝟙_ _) := by
      let := Scheme.ProEt.isContinuous_overPullback (𝟙 X)
      exact Functor.ε_sheafPushforwardContinuous_of_iso_id
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    erw [hε]
    have hn := (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.naturality
      (ProEtale.cupConstantIso P X).inv
    dsimp only [Functor.id_map] at hn
    calc
      _ = (ProEtale.cupConstantIso P X).hom ≫
          (ProEtale.cupConstantIso P X).inv ≫
          (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app
            (P.constant X) := congrArg (fun k ↦ (ProEtale.cupConstantIso P X).hom ≫ k)
              hn.symm
      _ = _ := by rw [Iso.hom_inv_id_assoc]; rfl

private theorem restriction_full_isIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : IsIso (P.functorialCupRestriction pro (𝟙 X)) := by
  rw [restriction_full]
  infer_instance

private theorem localization_full (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupLocalizationFullSupport pro := by
  unfold FunctorialCupLocalizationFullSupport
  intro X _aX a r
  have := restriction_full_isIso P pro X
  exact ((asIso ((P.functorialCupSingle pro X).map
    (P.functorialCupRestriction pro (𝟙 X)))).symm.homFromEquiv).bijective

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

private theorem exchange_normalized (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :
    (P.functorialCupInverseImage pro v).map (P.functorialCupRestriction pro i) ≫
        (P.functorialCupExchange pro i j v g sq).hom =
      (P.functorialCupConstantPullback pro v).hom ≫ P.functorialCupRestriction pro j := by
  cases pro <;> exact (P.functorialCupExchange_existsUnique _ i j v g sq).choose_spec.1

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

private theorem localization_forget (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupLocalizationForgetSupport pro := by
  unfold FunctorialCupLocalizationForgetSupport
  intro C X D Y i j hi hj v g sq aX a r α
  have : (P.functorialCupInverseImage pro v).Additive :=
    P.functorialCupInverseImage_additive pro v
  have : PreservesFiniteLimits (P.functorialCupInverseImage pro v) :=
    P.functorialCupInverseImage_limits pro v
  have : PreservesFiniteColimits (P.functorialCupInverseImage pro v) :=
    P.functorialCupInverseImage_colimits pro v
  have h := normalized_source_square
    (hB := P.functorialCupHasDerived pro X) (hD := P.functorialCupHasDerived pro Y)
    (P.functorialCupInverseImage pro v)
    (P.functorialCupRestriction pro i) (P.functorialCupRestriction pro j)
    (P.functorialCupConstantPullback pro v) (P.functorialCupExchange pro i j v g sq)
    (P.functorialCupTwistPullback pro v aX r)
    (exchange_normalized P pro i j v g sq) a α
  exact h

private theorem localization_open (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupLocalizationOpenRestriction pro := by
  unfold FunctorialCupLocalizationOpenRestriction
  intro C X D Y i j hi hj v g sq aX a r α
  have : (P.functorialCupInverseImage pro v).Additive :=
    P.functorialCupInverseImage_additive pro v
  have : PreservesFiniteLimits (P.functorialCupInverseImage pro v) :=
    P.functorialCupInverseImage_limits pro v
  have : PreservesFiniteColimits (P.functorialCupInverseImage pro v) :=
    P.functorialCupInverseImage_colimits pro v
  have h := normalized_source_square
    (hB := P.functorialCupHasDerived pro X) (hD := P.functorialCupHasDerived pro Y)
    (P.functorialCupInverseImage pro v)
    (P.functorialCupOpenInclusion pro i) (P.functorialCupOpenInclusion pro j)
    (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose
    (P.functorialCupConstantPullback pro v)
    (P.functorialCupTwistPullback pro v aX r)
    (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose_spec.1 a α
  exact h.symm

private theorem localization_boundary (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupLocalizationBoundary pro := by
  unfold FunctorialCupLocalizationBoundary
  intro C X D Y i j hi hj v g sq aX a r α
  let F := P.functorialCupInverseImage pro v
  have : F.Additive := P.functorialCupInverseImage_additive pro v
  have : PreservesFiniteLimits F := P.functorialCupInverseImage_limits pro v
  have : PreservesFiniteColimits F := P.functorialCupInverseImage_colimits pro v
  let e₁ := (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose
  let e₂ := P.functorialCupConstantPullback pro v
  let e₃ := P.functorialCupExchange pro i j v g sq
  have h := normalized_boundary_square
    (hB := P.functorialCupHasDerived pro X) (hD := P.functorialCupHasDerived pro Y) F
    (P.functorialCupSequence_shortExact pro i)
    (P.functorialCupSequence_shortExact pro j) e₁ e₂ e₃
    (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose_spec.1
    (exchange_normalized P pro i j v g sq)
    (P.functorialCupTwistPullback pro v aX r) a α
  simpa only [functorialCupPullback, functorialCupOpenPullback,
    functorialCupBoundary, functorialCupConnecting, functorialCupSingle,
    functorialCupSourceObject, functorialCupTarget, FunctorialCupH, functorialCupSequence,
    e₁, e₃, F] using h

/-- Pullback, localization, concrete Kummer identities and graded cup laws on both
small sites, identified by their canonical site comparison.
Source: Stacks Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

Proof:
1. Put m=ell^n. It annihilates A at every positive coefficient level. Apply
lem-asd-etale-finite-twist-pullback to its roots line, powers and duals. The local
primitive-root descriptions and lem-pur-twist-sheaf-locally-free identify the
projection-induced pro-etale twist and root coefficient map with this finite line.
Compare the identical root sections by lem-cbc-abelian-etale-proetale-cohomology-comparison
and lem-sf-comparison-pullback-exact. Every twist is a flat rank-one line.
2. Use lem-pur-etale-closed-constant-tensor: closed coefficients are flat, and the
normalized exchange and tensor multiplication are invertible and coherent. This
constructs the etale analogue of def-pur-supported-cup without exceptional base change.
3. Total tensor has its usual associator and Koszul symmetry. On homogeneous
cochains of degrees p,q the symmetry is (-1)^(pq). The two differential signs agree.
Descend these constraints through flat-term K-flat representatives using
lem-weil-pbc-site-derived-tensor-descent and lem-pc-kflat-closure. The canonical
ringed-topos tensor pullback comparison respects them termwise.
4. Use lem-amb-closed-support-hom and prop-weil-pbc-inverse-image-modules-exact
to pull back a representative as tau[a] v inverse(alpha) b inverse. Evaluation at 1
on injective representatives identifies this with the usual support-kernel pullback:
lem-weil-pbc-ext-exact-functor-cocycle and lem-weil-pbc-site-cohomology-pullback give
the normalization. Negative degrees vanish. Naturality of the actual source
short exact sequence gives restriction and boundary compatibility, with the
boundary convention of thm-pur-with-support-exactness. Unit-normalized exchanges
compose and are identities. For full support this is ordinary pullback.
5. Apply lem-pur-shifted-tensor-morphism-calculus to the flat support sources and
rank-one targets. Its sign is (-1)^(bp), exactly cupTensorShiftIso. Biadditivity
and scalar linearity give bilinearity. Its associativity and signed symmetry,
the source multiplications from Step 2 and the twist multiplications from Step 1
give associativity and (-1)^(ab) symmetry. Its pullback equation cancels the
normalized source exchanges and gives the cup pullback equality.
6. Evaluate comparison of a closed source on every weakly etale Y over X.
lem-cbc-comparison-pullback-sections and etale base change identify it with
etale constants on Y times_X C; degree-zero comparison identifies these with
pro-etale constants. Restriction and multiplication of the same local constants
identify the two coefficient multiplication maps and their flat derived maps.
No conservativity of pro-etale geometric stalks is asserted.
7. Full faithfulness in thm-weil-pbc-site-comparison and the supported Hom models
give the comparison bijections. lem-weil-pbc-comparison-pullback gives their
pullback square. lem-cbc-proetale-extension-zero-comparison preserves the open
counit by adjunction; together with Step 6 this identifies both arrows of the
source short exact sequence. The exact-functor single-delta formula
lem-weil-pbc-exact-functor-ses-triangle-image identifies the actual boundary,
including its sign. Step 5 then identifies the cups, and every pro-etale class
comes from an etale class, transporting all laws.
8. The Kummer sequence is short exact by lem-amb-kummer-any-base. Its connecting
map is additive by lem-weil-pbc-right-derived-universal-delta-functor. Pullback of
units commutes with powers and roots, giving naturality of its connecting map
by lem-weil-pbc-site-cohomology-pullback. The scalar extension sends a root to
that root tensor 1 and commutes with pullback. Def-pur-frame-class specifies
the concrete pro-etale class by comparison and this very root coefficient map,
so both Kummer identities and their site comparison follow. -/
theorem supportedCupFunctoriality (P : PurityFiniteSetting.{u}) :
    (∀ pro : Bool, P.FunctorialCupAlgebraLaws pro ∧ P.FunctorialCupLocalizationLaws pro) ∧
      P.FunctorialCupComparisonLaws := by
  refine ⟨?_, supportedCupComparison P⟩
  intro pro
  refine ⟨supportedCupAlgebra P pro, ?_⟩
  exact {
    full_support := localization_full P pro
    forget_support := localization_forget P pro
    open_restriction := localization_open P pro
    boundary := localization_boundary P pro
  }

set_option backward.isDefEq.respectTransparency false in
end WeilConjectures.PurityFiniteSetting
