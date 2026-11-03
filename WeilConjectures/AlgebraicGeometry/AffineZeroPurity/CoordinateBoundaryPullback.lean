/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import all WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Pullback of an individual realized coordinate boundary -/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] PurityFiniteSetting.Coefficient PurityFiniteSetting.Ring
  PurityFiniteSetting.coefficientCommRing PurityFiniteSetting.ringCommRing
  AffineLinePurity.Ring Scheme.finiteTateCoefficient
  PurityFiniteSetting.constant PurityFiniteSetting.constantEtale
  Etale.ordinaryFiniteConstant Etale.constantModuleSheaf Etale.closedConstantModule

set_option allowUnsafeReducibility true in
attribute [local reducible] setting AffineLinePurity.Ring
  DerivedCategory.singleFunctor
  Etale.ordinaryFiniteConstant Etale.ordinaryFiniteLine Etale.DerivedCategoryModule
  Etale.ordinaryFiniteDegreeZero
  PurityFiniteSetting.constant PurityFiniteSetting.constantEtale
  Etale.ordinaryFinitePullback Etale.ordinaryFiniteSingleFunctor
  PurityFiniteSetting.functorialCupCategory
  PurityFiniteSetting.functorialCupSheaves PurityFiniteSetting.functorialCupTopology
  PurityFiniteSetting.functorialCupAbelian PurityFiniteSetting.functorialCupMonoidal
  PurityFiniteSetting.functorialCupHasDerived PurityFiniteSetting.functorialCupSource
  PurityFiniteSetting.functorialCupInverseImage PurityFiniteSetting.functorialCupConstant
  PurityFiniteSetting.functorialCupRestriction PurityFiniteSetting.functorialCupComparisonFunctor

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors

private theorem exchange_square_of_normalization
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (FX : C ⥤ E) (FY : D ⥤ F) (U : C ⥤ D) (V : E ⥤ F)
    (τ : FX ⋙ V ≅ U ⋙ FY)
    {A S : C} {A' S' : D} {T : E} {T' : F}
    (ρ : A ⟶ S) (ρ' : A' ⟶ S') (σ : FX.obj A ⟶ T) (σ' : FY.obj A' ⟶ T')
    (ei : FX.obj S ≅ T) (ej : FY.obj S' ≅ T')
    (e : U.obj S ≅ S') (q : U.obj A ≅ A') (q' : V.obj (FX.obj A) ≅ FY.obj A')
    (b : V.obj T ≅ T')
    (hi : FX.map ρ ≫ ei.hom = σ) (hj : FY.map ρ' ≫ ej.hom = σ')
    (he : U.map ρ ≫ e.hom = q.hom ≫ ρ')
    (hb : V.map σ ≫ b.hom = q'.hom ≫ σ')
    (hq : τ.hom.app A ≫ FY.map q.hom = q'.hom)
    [Epi (V.map (FX.map ρ))] :
    V.map ei.hom ≫ b.hom = τ.hom.app S ≫ FY.map e.hom ≫ ej.hom := by
  apply (cancel_epi (V.map (FX.map ρ))).mp
  rw [← V.map_comp_assoc, hi, hb]
  rw [reassoc_of% τ.hom.naturality ρ]
  change q'.hom ≫ σ' =
    τ.hom.app A ≫ FY.map (U.map ρ) ≫ FY.map e.hom ≫ ej.hom
  rw [← FY.map_comp_assoc, he, FY.map_comp, Category.assoc, hj, ← Category.assoc, hq]

private theorem realized_arrow_pullback
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (FX : C ⥤ E) (FY : D ⥤ F) (U : C ⥤ D) (V : E ⥤ F)
    (τ : FX ⋙ V ≅ U ⋙ FY)
    {S T : C} {S' T' : D} {M : E} {M' : F}
    (ei : FX.obj S ≅ M) (ej : FY.obj S' ≅ M')
    (b : V.obj M ≅ M') (a : U.obj S ⟶ S') (l : U.obj T ⟶ T')
    (hs : V.map ei.hom ≫ b.hom = τ.hom.app S ≫ FY.map a ≫ ej.hom)
    (α : S ⟶ T) (α' : S' ⟶ T')
    (hα : a ≫ α' = U.map α ≫ l) :
    b.inv ≫ V.map (ei.inv ≫ FX.map α) ≫ τ.hom.app T ≫ FY.map l =
      ej.inv ≫ FY.map α' := by
  apply (cancel_epi b.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, V.map_comp]
  apply (cancel_epi (V.map ei.hom)).mp
  simp only [← V.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% τ.hom.naturality α, reassoc_of% hs]
  simp only [Iso.hom_inv_id_assoc, ← FY.map_comp, hα]

private theorem exact_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : C ⥤ B) (H : D ⥤ E) (I : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (σ : F ⋙ H ≅ G ⋙ I) (M : C) :
    (Functor.mapDerivedCategoryCompIso F H).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryNatIso σ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (Functor.mapDerivedCategoryCompIso G I).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      I.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) =
    H.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
      (DerivedCategory.singleFunctor E 0).map (σ.hom.app M) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F H).hom.app
    ((DerivedCategory.singleFunctor C 0).obj M))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (DerivedCategory.singleFunctor E 0).map (σ.hom.app M))
    (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F H M).symm

private theorem exact_single_transport
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : C ⥤ B) (H : D ⥤ E) (I : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (σ : F ⋙ H ≅ G ⋙ I) {S : C} {S' : B} {M : D} {M' : E}
    (ei : F.obj S ≅ M) (ej : I.obj S' ≅ M')
    (a : G.obj S ⟶ S') (b : H.obj M ≅ M')
    (hs : H.map ei.hom ≫ b.hom = σ.hom.app S ≫ I.map a ≫ ej.hom) :
    H.mapDerivedCategory.map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S ≫
          (DerivedCategory.singleFunctor D 0).map ei.hom) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor E 0).map b.hom =
    (Functor.mapDerivedCategoryCompIso F H).inv.app
        ((DerivedCategory.singleFunctor C 0).obj S) ≫
      (Functor.mapDerivedCategoryNatIso σ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj S) ≫
      (Functor.mapDerivedCategoryCompIso G I).hom.app
        ((DerivedCategory.singleFunctor C 0).obj S) ≫
      I.mapDerivedCategory.map
        ((G.mapDerivedCategorySingleFunctor 0).hom.app S ≫
          (DerivedCategory.singleFunctor B 0).map a) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app S' ≫
      (DerivedCategory.singleFunctor E 0).map ej.hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (H.mapDerivedCategorySingleFunctor 0).hom.naturality ei.hom]
  rw [← (DerivedCategory.singleFunctor E 0).map_comp, hs,
    (DerivedCategory.singleFunctor E 0).map_comp,
    (DerivedCategory.singleFunctor E 0).map_comp]
  rw [← reassoc_of% exact_single_square F G H I σ S]
  rw [reassoc_of% (I.mapDerivedCategorySingleFunctor 0).hom.naturality a]

private theorem derived_single_transport
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (F : C ⥤ D) (G : C ⥤ B) (H : D ⥤ E) (I : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (σ : F ⋙ H ≅ G ⋙ I)
    (LG : DerivedCategory C ⥤ DerivedCategory B)
    (LH : DerivedCategory D ⥤ DerivedCategory E)
    (ηG : LG ≅ G.mapDerivedCategory) (ηH : LH ≅ H.mapDerivedCategory)
    {S : C} {S' : B} {M : D} {M' : E}
    (ei : F.obj S ≅ M) (ej : I.obj S' ≅ M')
    (a : G.obj S ⟶ S') (b : H.obj M ≅ M')
    (hs : H.map ei.hom ≫ b.hom = σ.hom.app S ≫ I.map a ≫ ej.hom) :
    let e := (F.mapDerivedCategorySingleFunctor 0).app S ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso ei
    let e' := (I.mapDerivedCategorySingleFunctor 0).app S' ≪≫
      (DerivedCategory.singleFunctor E 0).mapIso ej
    let τ := Functor.isoWhiskerLeft F.mapDerivedCategory
        ηH ≪≫
      (Functor.mapDerivedCategoryCompIso F H).symm ≪≫
      Functor.mapDerivedCategoryNatIso σ ≪≫ Functor.mapDerivedCategoryCompIso G I ≪≫
      Functor.isoWhiskerRight ηG.symm
        I.mapDerivedCategory
    LH.map e.hom ≫
        ηH.hom.app ((DerivedCategory.singleFunctor D 0).obj M) ≫
        (H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor E 0).map b.hom =
      τ.hom.app ((DerivedCategory.singleFunctor C 0).obj S) ≫
        I.mapDerivedCategory.map
          (ηG.hom.app ((DerivedCategory.singleFunctor C 0).obj S) ≫
            (G.mapDerivedCategorySingleFunctor 0).hom.app S ≫
            (DerivedCategory.singleFunctor B 0).map a) ≫ e'.hom := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [Category.assoc]
  rw [reassoc_of% ηH.hom.naturality]
  rw [exact_single_transport F G H I σ ei ej a b hs]
  rw [← I.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rfl

set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
private theorem closed_exchange_comparison (Q : PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i'] (v : X' ⟶ X) (p : Z' ⟶ Z)
    (sq : ChosenCartesianSquare p i' i v) :
    (upperStar (ModuleCat.{u + 1} Q.Coefficient) v).map
        ((lowerStarComparisonUpperStarBaseChange i
          (ModuleCat.{u + 1} Q.Coefficient)).app (Q.constantEtale Z)) ≫
      (Q.functorialCupExchange true i i' v p sq).hom =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Q.Coefficient) v).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Q.Coefficient) i).obj (Q.constantEtale Z)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient) X').map
        (Etale.supportedConstantExchange Q.Coefficient i i' v p sq.toCommSq) ≫
      (lowerStarComparisonUpperStarBaseChange i'
        (ModuleCat.{u + 1} Q.Coefficient)).app (Q.constantEtale Z') := by
  let B := ModuleCat.{u + 1} Q.Coefficient
  let FX := Q.functorialCupComparisonFunctor X
  let FY := Q.functorialCupComparisonFunctor X'
  let U := Q.functorialCupInverseImage false v
  let V := Q.functorialCupInverseImage true v
  have hs : IsPullback p i' i v :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have := Etale.isIso_baseChangeMap_of_isFinite B hs
  have : IsIso (Etale.supportedConstantExchange Q.Coefficient i i' v p sq.toCommSq) := by
    unfold Etale.supportedConstantExchange
    infer_instance
  have := isIso_lowerStarComparisonUpperStarBaseChange i B
  have := isIso_lowerStarComparisonUpperStarBaseChange i' B
  let ei := asIso ((lowerStarComparisonUpperStarBaseChange i B).app (Q.constantEtale Z))
  let ej := asIso ((lowerStarComparisonUpperStarBaseChange i' B).app (Q.constantEtale Z'))
  let e := asIso (Etale.supportedConstantExchange Q.Coefficient i i' v p sq.toCommSq)
  have hi : FX.map (Q.functorialCupRestriction false i) ≫ ei.hom =
      Q.functorialCupRestriction true i := by
    change (comparisonUpperStar B X).map
      (Etale.closedConstantSectionMap Q.Coefficient i) ≫ _ = _
    rw [PurityFiniteSetting.section_unit]
    exact (comparison_restriction Q i).symm
  have hj : FY.map (Q.functorialCupRestriction false i') ≫ ej.hom =
      Q.functorialCupRestriction true i' := by
    change (comparisonUpperStar B X').map
      (Etale.closedConstantSectionMap Q.Coefficient i') ≫ _ = _
    rw [PurityFiniteSetting.section_unit]
    exact (comparison_restriction Q i').symm
  have he := etale_closed_exchange_normalization Q i i' v p sq
  have hb := (Q.functorialCupExchange_existsUnique true i i' v p sq).choose_spec.1
  have : Epi (Q.functorialCupRestriction false i) :=
    PurityFiniteSetting.section_epi Q.Coefficient i
  have : V.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels V
  have : Epi (FX.map (Q.functorialCupRestriction false i)) := FX.map_epi _
  have : Epi (V.map (FX.map (Q.functorialCupRestriction false i))) := V.map_epi _
  apply exchange_square_of_normalization FX FY U V
    (comparisonUpperStarCompUpperStarIso B v)
    (Q.functorialCupRestriction false i) (Q.functorialCupRestriction false i')
    (Q.functorialCupRestriction true i) (Q.functorialCupRestriction true i')
    ei ej e (Q.functorialCupConstantPullback false v)
    (Q.functorialCupConstantPullback true v)
    (Q.functorialCupExchange true i i' v p sq) hi hj he hb
  simp only [PurityFiniteSetting.functorialCupConstantPullback,
    PurityFiniteSetting.frameConstantPullback, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rfl

private theorem annihilates_coefficient (P : PurityFiniteSetting.{u}) (n : ℕ) :
    ((P.coefficients.l ^ (n + 1 + 1) : ℕ) : (setting P n).Coefficient) = 0 := by
  with_unfolding_all exact annihilates (setting P n)

set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
private theorem ordinaryBoundary_normalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    Etale.SupportedKummerBoundary (setting P n).Coefficient
      (P.coefficients.l ^ (n + 1 + 1)) (annihilates_coefficient P n)
      (inclusion B c i) (coordinate_cartier B c i)
      (exponentUnit (setting P n) _ (towerBase aB c))
      (ordinaryBoundary P n B aB c i) := by
  have h := (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.1
  unfold Etale.CartierEtaleKummerNormalization at h
  unfold ordinaryBoundary
  with_unfolding_all exact (h n (n + 1) (annihilates_coefficient P n) (inclusion B c i)
    (coordinate_cartier B c i)
    (AffineLinePurity.primeUnit (setting P n) _ (towerBase aB c)))

set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
private theorem ordinaryBoundary_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (c : ℕ) (i : Fin c) (p : divisor B' c i ⟶ divisor B c i)
    (sq : ChosenCartesianSquare p (inclusion B' c i) (inclusion B c i) (spaceMap g c)) :
    (Ext.mk₀ (Etale.supportedConstantExchange (setting P n).Coefficient
      (inclusion B c i) (inclusion B' c i) (spaceMap g c) p sq.toCommSq)).comp
      (ordinaryBoundary P n B' (g ≫ aB) c i) (zero_add 2) =
    ((ordinaryBoundary P n B aB c i).mapExactFunctor
      (Etale.upperStar (ModuleCat.{u + 1} (setting P n).Coefficient) (spaceMap g c))).comp
      (Ext.mk₀ ((Etale.projectiveLineTraceTransport
        (P.coefficients.l ^ (n + 1 + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (setting P n).Coefficient (annihilates_coefficient P n)).line
        (spaceMap g c) (exponentUnit (setting P n) _ (towerBase aB c))).hom)
      (add_zero 2) := by
  exact Etale.supported_kummer_boundary_pullback _ _
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (setting P n).Coefficient
    (annihilates_coefficient P n) (exponentUnit (setting P n) _ (towerBase aB c))
    (inclusion B c i) (coordinate_cartier B c i) (ordinaryBoundary P n B aB c i)
    (ordinaryBoundary_normalized P n B aB c i) _ (inclusion B' c i)
    (spaceMap g c) p
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
    (coordinate_cartier B' c i)
    (ordinaryBoundary P n B' (g ≫ aB) c i)
    (ordinaryBoundary_normalized P n B' (g ≫ aB) c i)

set_option maxHeartbeats 2000000 in
-- Compute the exact comparison before specializing the coefficient conventions.
private theorem ordinary_class_derived_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i'] (v : X' ⟶ X) (p : Z' ⟶ Z)
    (sq : CommSq p i' i v) (hX : IsUnit (N : Γ(X, ⊤)))
    (κ : Ext ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A Z)) (X.finiteEtaleTateLine N A hA) 2)
    (κ' : Ext ((Etale.lowerStar (ModuleCat.{u + 1} A) i').obj
        (Etale.ordinaryFiniteConstant A Z')) (X'.finiteEtaleTateLine N A hA) 2)
    (hκ : (Ext.mk₀ (Etale.supportedConstantExchange A i i' v p sq)).comp κ'
        (zero_add 2) =
      (κ.mapExactFunctor (Etale.upperStar (ModuleCat.{u + 1} A) v)).comp
        (Ext.mk₀ (t.line v hX).hom) (add_zero 2)) :
    (Etale.ordinaryFiniteSinglePullbackIso A v).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          (Etale.supportedConstantExchange A i i' v p sq) ≫ κ'.hom =
      (Etale.ordinaryFinitePullback A v).map κ.hom ≫
        (Etale.ordinaryFiniteShiftedLinePullback A N hA t v hX).hom := by
  have h := congrArg Ext.hom hκ
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom, ShiftedHom.map, Category.assoc] at h
  have h' := congrArg
    (fun f ↦ (Etale.ordinaryFiniteSinglePullbackIso A v).hom.app _ ≫ f) h
  simp only [Etale.ordinaryFiniteSinglePullbackIso,
    Etale.ordinaryFiniteSingleExactPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc] at h'
  erw [← reassoc_of% (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v).hom.naturality κ.hom] at h'
  simp only [Etale.ordinaryFiniteShiftedLinePullback,
    Etale.shiftedSinglePullbackIsoWith, Etale.ordinaryFiniteSinglePullbackIso,
    Etale.ordinaryFiniteSingleExactPullbackIso,
    Etale.ordinaryFinitePullback, Etale.ordinaryFiniteSingleFunctor,
    Etale.ordinaryFiniteDegreeZero, Etale.ordinaryFiniteLine,
    Functor.CommShift.ofIso_commShiftIso_hom_app, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] at h' ⊢
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact h'

set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
private theorem ordinaryBoundary_derived_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (c : ℕ) (i : Fin c) (p : divisor B' c i ⟶ divisor B c i)
    (sq : ChosenCartesianSquare p (inclusion B' c i) (inclusion B c i) (spaceMap g c)) :
    (Etale.ordinaryFiniteSinglePullbackIso (setting P n).Coefficient
        (spaceMap g c)).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Etale.supportedConstantExchange (setting P n).Coefficient
          (inclusion B c i) (inclusion B' c i) (spaceMap g c) p sq.toCommSq) ≫
      (ordinaryBoundary P n B' (g ≫ aB) c i).hom =
    (Etale.ordinaryFinitePullback (setting P n).Coefficient (spaceMap g c)).map
        (ordinaryBoundary P n B aB c i).hom ≫
      (Etale.ordinaryFiniteShiftedLinePullback (setting P n).Coefficient
        (P.coefficients.l ^ (n + 1 + 1)) (annihilates_coefficient P n)
        (Etale.projectiveLineTraceTransport _
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) _
          (annihilates_coefficient P n)) (spaceMap g c)
        (exponentUnit (setting P n) _ (towerBase aB c))).hom := by
  with_unfolding_all exact (ordinary_class_derived_pullback
    (setting P n).Coefficient (P.coefficients.l ^ (n + 1 + 1))
    (annihilates_coefficient P n)
    (Etale.projectiveLineTraceTransport _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) _ (annihilates_coefficient P n))
    (inclusion B c i) (inclusion B' c i) (spaceMap g c) p sq.toCommSq
    (exponentUnit (setting P n) _ (towerBase aB c))
    (ordinaryBoundary P n B aB c i) (ordinaryBoundary P n B' (g ≫ aB) c i)
    (ordinaryBoundary_pullback P n g aB c i p sq))

-- Match the category-instance proofs captured in the recorded derived module category.

set_option maxHeartbeats 8000000 in
-- Keep site coherence independent of the large specialized coefficient record.
private theorem realized_boundary_pullback (Q : PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i'] (v : X' ⟶ X) (p : Z' ⟶ Z)
    (sq : ChosenCartesianSquare p i' i v)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Q.Coefficient))
    (L' : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Q.Coefficient))
    (κ : Ext ((Etale.lowerStar (ModuleCat.{u + 1} Q.Coefficient) i).obj
      (Q.constantEtale Z)) L 2)
    (κ' : Ext ((Etale.lowerStar (ModuleCat.{u + 1} Q.Coefficient) i').obj
      (Q.constantEtale Z')) L' 2)
    (l : (Etale.ordinaryFinitePullback Q.Coefficient v).obj
      (((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj L')⟦(2 : ℤ)⟧)
    (hκ : (Etale.ordinaryFiniteSinglePullbackIso Q.Coefficient v).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          (Etale.supportedConstantExchange Q.Coefficient i i' v p sq.toCommSq) ≫
          κ'.hom = (Etale.ordinaryFinitePullback Q.Coefficient v).map κ.hom ≫ l) :
    (pullbackSingle Q.Coefficient v _ _
        (Q.functorialCupExchange true i i' v p sq)).inv ≫
      (inverseImage Q.Coefficient v).map
        (realizeBoundary Q.Coefficient i (Q.constantEtale Z) L κ) ≫
      (geoP1PullComparison Q.Coefficient v).hom.app _ ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient) X').mapDerivedCategory.map l =
    realizeBoundary Q.Coefficient i' (Q.constantEtale Z') L' κ' := by
  let A := ModuleCat.{u + 1} Q.Coefficient
  let U := Etale.upperStar A v
  let V := upperStar A v
  let ν := comparisonUpperStar A X
  let ν' := comparisonUpperStar A X'
  let S := (Etale.lowerStar A i).obj (Q.constantEtale Z)
  let S' := (Etale.lowerStar A i').obj (Q.constantEtale Z')
  have := isIso_lowerStarComparisonUpperStarBaseChange i A
  have := isIso_lowerStarComparisonUpperStarBaseChange i' A
  let eS := asIso ((lowerStarComparisonUpperStarBaseChange i A).app (Q.constantEtale Z))
  let eS' := asIso ((lowerStarComparisonUpperStarBaseChange i' A).app (Q.constantEtale Z'))
  let ei := (ν.mapDerivedCategorySingleFunctor 0).app S ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eS
  let ej := (ν'.mapDerivedCategorySingleFunctor 0).app S' ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eS'
  let b := pullbackSingle Q.Coefficient v _ _
    (Q.functorialCupExchange true i i' v p sq)
  let e := Etale.supportedConstantExchange Q.Coefficient i i' v p sq.toCommSq
  let a := (Etale.ordinaryFiniteSinglePullbackIso Q.Coefficient v).hom.app S ≫
    (DerivedCategory.singleFunctor _ 0).map e
  let τ := comparisonUpperStarCompUpperStarIso A v
  have hs : V.leftDerivedFunctor.map ei.hom ≫ b.hom =
      (geoP1PullComparison Q.Coefficient v).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj S) ≫
        ν'.mapDerivedCategory.map a ≫ ej.hom := by
    have ht := derived_single_transport ν U V ν' τ
      U.leftDerivedFunctor V.leftDerivedFunctor
      U.leftDerivedFunctorIsoMapDerivedCategory V.leftDerivedFunctorIsoMapDerivedCategory
      eS eS' e (Q.functorialCupExchange true i i' v p sq)
      (closed_exchange_comparison Q i i' v p sq)
    simp only [b, pullbackSingle, ei, ej,
      geoP1PullComparison, a, Etale.ordinaryFiniteSinglePullbackIso,
      Etale.ordinaryFiniteSingleExactPullbackIso, Iso.trans_hom, Iso.app_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.mapIso_hom, Category.assoc] at ht ⊢
    with_unfolding_all exact ht
  have h := realized_arrow_pullback ν.mapDerivedCategory ν'.mapDerivedCategory
    U.leftDerivedFunctor V.leftDerivedFunctor (geoP1PullComparison Q.Coefficient v)
    ei ej b a l hs κ.hom κ'.hom (by
      simp only [a, Category.assoc] at hκ ⊢
      with_unfolding_all exact hκ)
  have hβ : realizeBoundary Q.Coefficient i (Q.constantEtale Z) L κ =
      ei.inv ≫ ν.mapDerivedCategory.map κ.hom := by
    with_unfolding_all simp only [realizeBoundary, ei, Iso.trans_inv,
      Iso.app_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]
    with_unfolding_all rfl
  have hβ' : realizeBoundary Q.Coefficient i' (Q.constantEtale Z') L' κ' =
      ej.inv ≫ ν'.mapDerivedCategory.map κ'.hom := by
    with_unfolding_all simp only [realizeBoundary, ej, Iso.trans_inv,
      Iso.app_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]
    with_unfolding_all rfl
  rw [hβ, hβ']
  with_unfolding_all exact h

set_option maxHeartbeats 8000000 in
-- Exact site and scalar comparison normalization needs additional elaboration work.
/-- Each actual realized coordinate boundary is preserved by arbitrary base change.
Source: normalized Cartier-Kummer naturality and exact site comparison;
coordinate pullback proof Step 1
(blueprint: lem-pur-coordinate-boundary-pullback).

Proof: the coordinate variable pulls back to the same variable, which remains
a nonzerodivisor over the new base. Apply supported_kummer_boundary_pullback
to the two normalized ordinaryBoundary classes at the common exponent
ell^(n+2). The source exchange is fixed by restriction of the coefficient unit,
and the finite root transport by its root tensors. Exact site comparison
commutes with inverse image through its adjunction mate. Its single-complex
comparison is natural. Conjugate the ordinary Ext equality by these two
comparisons and the closed site exchanges defining realizeBoundary.
The supported-constant quotient normalization identifies the resulting source
comparison with functorialCupExchange, and the root normalization identifies
the target with shiftedLinePullback. The inverse comparison on the source
then gives the displayed derived-arrow equality. No flatness of g is used;
the argument also covers an empty base and zero coefficients. -/
theorem coordinateBoundary_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (c : ℕ) (i : Fin c) (p : divisor B' c i ⟶ divisor B c i)
    (sq : ChosenCartesianSquare p (inclusion B' c i) (inclusion B c i) (spaceMap g c)) :
    (pullbackSingle (setting P n).Coefficient (spaceMap g c) _ _
        ((setting P n).functorialCupExchange true (inclusion B c i)
          (inclusion B' c i) (spaceMap g c) p sq)).inv ≫
      (inverseImage (setting P n).Coefficient (spaceMap g c)).map
        (boundary P n B aB c i) ≫
      (shiftedLinePullback (setting P n) (spaceMap g c) (towerBase aB c)).hom =
    boundary P n B' (g ≫ aB) c i := by
  let Q := setting P n
  let v := spaceMap g c
  let l := Etale.ordinaryFiniteShiftedLinePullback Q.Coefficient
    (P.coefficients.l ^ (n + 1 + 1)) (annihilates_coefficient P n)
    (Etale.projectiveLineTraceTransport _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) _ (annihilates_coefficient P n)) v
    (exponentUnit Q _ (towerBase aB c))
  have h := realized_boundary_pullback Q (inclusion B c i) (inclusion B' c i) v p sq
    _ _ (ordinaryBoundary P n B aB c i) (ordinaryBoundary P n B' (g ≫ aB) c i)
    l.hom (ordinaryBoundary_derived_pullback P n g aB c i p sq)
  have ht : (shiftedLinePullback Q v (towerBase aB c)).hom =
      (geoP1PullComparison Q.Coefficient v).hom.app _ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
          (iteratedAffineLine B' c)).mapDerivedCategory.map l.hom := by
    with_unfolding_all rfl
  rw [← ht] at h
  with_unfolding_all exact h

end AlgebraicGeometry.ProEtale.AffineZeroPurity
