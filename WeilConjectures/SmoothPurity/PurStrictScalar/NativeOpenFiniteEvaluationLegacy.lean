/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeGeometricFiniteEvaluationData
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarDerivedComparison
import all WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import all WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryOpenTransition
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import all WeilConjectures.SmoothPurity.Compact.CompactSupportNativeOpenTransition
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.PurCompactSupport.FiniteScalarPresentationCompatibility

/-! # Archived open finite evaluation of native systems

Historical proof retained during the condensed route switch. New code uses
Sheaf.Paper.NativeOpenFiniteEvaluation; the native support parent still needs
its own route-switch repair. This archive is not a condensed comparison.

Source: Stacks 03DI, 0D6E and 0E8I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
-- These are two definitionally equal presentations of the same ringed sequence site.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  WeilConjectures.PurStrictScalar.nativeConstantScalarMap
  WeilConjectures.PurStrictScalar.constantFiniteRingMap
  WeilConjectures.PurStrictScalar.constantFiniteChange
  WeilConjectures.PurStrictScalar.systemOpenMap
  WeilConjectures.PurStrictScalar.systemU
  AlgebraicGeometry.ProEtale.StrictTower.moduleJAdj
  AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarMap
  AlgebraicGeometry.ProEtale.VaryingRing.scalarTowerOpenAdj
  RingHom.ulift CategoryTheory.TwoSquare
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.coefficientSequenceCommRingSystem
  WeilConjectures.coefficientSequenceCommRingTransition
  WeilConjectures.coefficientSequenceEvaluation
  WeilConjectures.compactSupportSystemLevel
  WeilConjectures.compactSupportSystemQuotient
  AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
  AlgebraicGeometry.Scheme.sfConstantCoefficientIso
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  AlgebraicGeometry.Scheme.openSquarePullbackModel
  WeilConjectures.nativeSystemOpen
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
  WeilConjectures.SemilinearSections.evaluation
  WeilConjectures.PurStrictScalar.finiteRestriction
  WeilConjectures.PurStrictScalar.positiveRestriction
  WeilConjectures.PurStrictScalar.ordinaryFiniteRestriction
  AlgebraicGeometry.Scheme.proEtaleRingOpenExtension
  WeilConjectures.PurCompactSupport.openAdjunction
  AlgebraicGeometry.Scheme.pbcDerivedRestrict
  AlgebraicGeometry.ProEtale.VaryingRing.coefficientTransition
  AlgebraicGeometry.ProEtale.VaryingRing.scalarTowerAdj
  AlgebraicGeometry.ProEtale.StrictTower.modulePullback
  AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage
  WeilConjectures.PurCompactSupport.finite
  WeilConjectures.PurStrictScalar.constants
attribute [local irreducible] CategoryTheory.constantSheaf
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
  systemPullMap_isIso systemOpenMap_isIso
  proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

private abbrev baseRing := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
private abbrev systemR := compactSupportSystemLevel l E
private abbrev systemQ := compactSupportSystemQuotient l E
private abbrev scalarMap := nativeConstantScalarMap l E

private def ordinaryIdentification (W : Scheme.{u}) (n : ℕ) :
    ordinaryFiniteRestriction l E W n ≅
      SemilinearSections.res
        (ProEtale.VaryingRing.ordinaryScalarMap (systemR l E) (baseRing l E)
          (scalarMap l E) W n) := by
  let m := n + 1
  let hm : 1 ≤ m := Nat.le_add_left 1 n
  let a := integralConstantToCompletionOfUniverses l E W
  let b := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (PurCompactSupport.projection l E m hm W)
  let d := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantFiniteChange l E m hm).map W)
  have h : a ≫ b = d := constantFiniteChange_projection l E W m hm
  change ordinaryPositiveRestriction l E W m hm ≅
    pbcRestrict ((constantFiniteChange l E m hm).map W)
  exact NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (b.hom.app U).hom
          (d.hom.app U).hom
          (congrArg (fun t ↦ (t.hom.app U).hom) h.symm) (M.val.obj U)).symm)
        (fun {_ _} f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)

-- Exactness instances in the two coordinate presentations have the same proof.
private instance nativeEvaluation_additive (W : Scheme.{u}) (n : ℕ) :
    ((coefficientSequenceEvaluation l E W n) :
      ProEtale.VaryingRing.Modules (systemR l E) (systemQ l E) W ⥤
        normalizedDVRModules l E W n).Additive :=
  coefficientSequenceEvaluation_additive l E W n

private instance nativeEvaluation_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits ((coefficientSequenceEvaluation l E W n) :
      ProEtale.VaryingRing.Modules (systemR l E) (systemQ l E) W ⥤
        normalizedDVRModules l E W n) :=
  coefficientSequenceEvaluation_limits l E W n

private instance nativeEvaluation_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits ((coefficientSequenceEvaluation l E W n) :
      ProEtale.VaryingRing.Modules (systemR l E) (systemQ l E) W ⥤
        normalizedDVRModules l E W n) :=
  coefficientSequenceEvaluation_colimits l E W n

private instance nativeLevelOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    ((moduleJ (systemR l E n) j) :
      normalizedDVRModules l E X n ⥤ normalizedDVRModules l E Y n).Additive :=
  moduleJ_additive (systemR l E n) j

private instance nativeLevelOpen_limits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteLimits ((moduleJ (systemR l E n) j) :
      normalizedDVRModules l E X n ⥤ normalizedDVRModules l E Y n) :=
  moduleJ_finiteLimits (systemR l E n) j

private instance nativeLevelOpen_colimits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteColimits ((moduleJ (systemR l E n) j) :
      normalizedDVRModules l E X n ⥤ normalizedDVRModules l E Y n) :=
  moduleJ_finiteColimits (systemR l E n) j

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem ordinaryIdentification_localize (W : Scheme.{u}) (n : ℕ) :
    Functor.mapDerivedCategoryNatIso (ordinaryIdentification l E W n) =
      positiveRestrictionIdentification l E W (n + 1) (Nat.le_add_left 1 n) := by
  rfl

private def canonicalEvaluation (W : Scheme.{u}) (n : ℕ) :
    systemRestriction l E W ⋙ (evaluation ℕᵒᵖ (Modules (baseRing l E) W)).obj (op n) ≅
      ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) W n ⋙
        SemilinearSections.res
          (ProEtale.VaryingRing.ordinaryScalarMap (systemR l E) (baseRing l E)
            (scalarMap l E) W n) :=
  evaluationRestrictionOrdinary l E W n ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E W n)
      (ordinaryIdentification l E W n)

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem normalized_apply {A B T : Type (u + 1)}
    (hA : A = T) (hB : B = T) (f : A → B)
    (hf : HEq f (id : T → T)) (x : A) : HEq (f x) x := by
  subst hA
  subst hB
  exact heq_of_eq (congrFun (eq_of_heq hf) x)

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem canonicalEvaluation_sections (W : Scheme.{u}) (n : ℕ)
    (N : coefficientSequenceModules.{u, u} l E W) (H : W.ProEtᵒᵖ)
    (x : (((systemRestriction l E W).obj N).obj (op n)).val.obj H) :
    HEq (((canonicalEvaluation l E W n).hom.app N).val.app H x) x := by
  have hA : ((((systemRestriction l E W).obj N).obj (op n)).val.obj H : Type (u + 1)) =
      (N.val.obj (op (n, H.unop)) : Type (u + 1)) := by
    rw [systemRestriction_eq]
    rfl
  change HEq (((evaluationRestrictionOrdinary l E W n).hom.app N).val.app H x) x
  exact normalized_apply hA rfl _
    ((evaluationRestriction_existsUnique l E W n).choose_spec.1 N H) x

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem systemProperEvaluationCube {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules.{u, u} l E X) :
    ((systemProperOrdinary l E j).hom.app N).app (op n) ≫
      (moduleDirectImage (baseRing l E) j).map
        ((canonicalEvaluation l E X n).hom.app N) =
    (canonicalEvaluation l E Y n).hom.app
        ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N) ≫
      (SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
        (systemR l E) (baseRing l E) (scalarMap l E) Y n)).map
        ((ProEtale.VaryingRing.moduleEvalP (systemR l E) (systemQ l E) j n).hom.app N) ≫
      (ProEtale.VaryingRing.scalarLevelDOrd
        (R := systemR l E) (B := baseRing l E) (ψ := scalarMap l E) j n).hom.app
          ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) X n).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro H
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hA : (((((systemRestriction l E Y).obj
      ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N)).obj
        (op n)).val.obj H) : Type (u + 1)) =
      (N.val.obj (op (n, (proEtaleBaseChange j).obj H.unop)) : Type (u + 1)) := by
    rw [systemRestriction_eq]
    rfl
  have hB : (((((systemRestriction l E X).obj N).obj (op n)).val.obj
      ((proEtaleBaseChange j).op.obj H)) : Type (u + 1)) =
      (N.val.obj (op (n, (proEtaleBaseChange j).obj H.unop)) : Type (u + 1)) := by
    rw [systemRestriction_eq]
    rfl
  have hd := normalized_apply hA hB
    (fun x ↦ (((((systemProperOrdinary l E j).hom.app N).app (op n)).val.app H) x))
    ((systemProperOrdinary_existsUnique l E j).choose_spec.1 N n H) x
  have hlX := canonicalEvaluation_sections l E X n N
    ((proEtaleBaseChange j).op.obj H)
      (((((systemProperOrdinary l E j).hom.app N).app (op n)).val.app H) x)
  have hlY := canonicalEvaluation_sections l E Y n
    ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N) H x
  have hp := (ProEtale.VaryingRing.moduleEvalP_existsUnique
    (systemR l E) (systemQ l E) j n).choose_spec.1
  let z := ProEtale.VaryingRing.unrestrictSection
    (ProEtale.VaryingRing.ordinaryScalarMap (systemR l E) (baseRing l E)
      (scalarMap l E) Y n)
    ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) Y n).obj
      ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N)) H
    (((canonicalEvaluation l E Y n).hom.app
      ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N)).val.app H x)
  let w := ProEtale.VaryingRing.directSection j n
    ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) X n).obj N) H
    ((((ProEtale.VaryingRing.moduleEvalP
      (systemR l E) (systemQ l E) j n).hom.app N).val.app H) z)
  have hq := ProEtale.VaryingRing.scalarLevelDOrd_sections
    (R := systemR l E) (B := baseRing l E) (ψ := scalarMap l E) j n
    ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) X n).obj N) H w
  have hp' := hp N H.unop (ProEtale.VaryingRing.evalSection Y n
    ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N) H z)
  change (((canonicalEvaluation l E X n).hom.app N).val.app
      ((proEtaleBaseChange j).op.obj H)
      (((((systemProperOrdinary l E j).hom.app N).app (op n)).val.app H) x)) =
    (((ProEtale.VaryingRing.scalarLevelDOrd
      (R := systemR l E) (B := baseRing l E) (ψ := scalarMap l E) j n).hom.app
        ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) X n).obj N)).val.app H w)
  apply eq_of_heq
  exact (hlX.trans hd).trans
    (((heq_of_eq (hq.trans hp')).trans hlY).symm)

private def pullSquare {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ) :=
  proEtaleRingRestrictionPullbackInv j
    (coefficients (baseRing l E) Y)
    (ProEtale.VaryingRing.coefficients (systemR l E) Y n)
    (coefficients (baseRing l E) X)
    (ProEtale.VaryingRing.coefficients (systemR l E) X n)
    (ProEtale.VaryingRing.ordinaryScalarMap
      (systemR l E) (baseRing l E) (scalarMap l E) Y n)
    (ProEtale.VaryingRing.ordinaryScalarMap
      (systemR l E) (baseRing l E) (scalarMap l E) X n)
    (constantRingIso (baseRing l E) j) (constantRingIso (systemR l E n) j)
    (proEtaleConstantInverseImageMap_naturality j (scalarMap l E n)).symm

private instance pullSquare_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ) :
    IsIso (pullSquare l E j n) := by
  unfold pullSquare
  infer_instance

private instance pullSquare_app_mono {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ)
    (M : Modules (systemR l E n) Y) : Mono ((pullSquare l E j n).app M) := by
  haveI := pullSquare_isIso l E j n
  infer_instance

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem canonicalPullCube {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules.{u, u} l E Y) :
    (eqToIso (evaluationPullback (baseRing l E) j n)).inv.app
        ((systemRestriction l E Y).obj M) ≫
      ((evaluation ℕᵒᵖ (Modules (baseRing l E) X)).obj (op n)).map
        ((systemPullMap l E j).app M) ≫
      (canonicalEvaluation l E X n).hom.app
        ((ProEtale.VaryingRing.pull (systemR l E) (systemQ l E) j).obj M) =
    (modulePullback (baseRing l E) j).map
        ((canonicalEvaluation l E Y n).hom.app M) ≫
      (pullSquare l E j n).app
        ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) Y n).obj M) ≫
      (SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
        (systemR l E) (baseRing l E) (scalarMap l E) X n)).map
        ((ProEtale.VaryingRing.moduleEvalG
          (systemR l E) (systemQ l E) j n).inv.app M) := by
  apply inverseMateCube
    (ProEtale.VaryingRing.moduleAdj (systemR l E) (systemQ l E) j)
    (ProEtale.VaryingRing.scalarTowerAdj (baseRing l E) j)
    (proEtaleRingModuleAdjunction j (coefficients (baseRing l E) Y)
      (coefficients (baseRing l E) X) (constantRingIso (baseRing l E) j))
    (proEtaleRingModuleAdjunction j
      (ProEtale.VaryingRing.coefficients (systemR l E) Y n)
      (ProEtale.VaryingRing.coefficients (systemR l E) X n)
      (constantRingIso (systemR l E n) j))
    (TwoSquare.mk _ _ _ _ (systemPullMap l E j))
    (TwoSquare.mk _ _ _ _
      (eqToIso (evaluationPullback (baseRing l E) j n)).inv)
    (TwoSquare.mk _ _ _ _
      (ProEtale.VaryingRing.moduleEvalG (systemR l E) (systemQ l E) j n).inv)
    (TwoSquare.mk _ _ _ _ (pullSquare l E j n))
    (canonicalEvaluation l E Y n) (canonicalEvaluation l E X n) ?_ M
  intro N
  have h1 : (mateEquiv
      (ProEtale.VaryingRing.moduleAdj (systemR l E) (systemQ l E) j)
      (ProEtale.VaryingRing.scalarTowerAdj (baseRing l E) j)
      (TwoSquare.mk _ _ _ _ (systemPullMap l E j))).natTrans =
        (systemProperOrdinary l E j).hom := by
    exact congrArg TwoSquare.natTrans (Equiv.apply_symm_apply _ _)
  have h2 := congr_app
    (ProEtale.VaryingRing.scalarTowerEvaluation_mate (B := baseRing l E) j n)
    ((systemRestriction l E X).obj N)
  have h3 := congr_app (ProEtale.VaryingRing.scalarEvalP_mate
    (R := systemR l E) (φ := systemQ l E) j n) N
  have h4 := congr_app (restrictionPullback_mate j
    (coefficients (baseRing l E) Y)
    (ProEtale.VaryingRing.coefficients (systemR l E) Y n)
    (coefficients (baseRing l E) X)
    (ProEtale.VaryingRing.coefficients (systemR l E) X n)
    (ProEtale.VaryingRing.ordinaryScalarMap
      (systemR l E) (baseRing l E) (scalarMap l E) Y n)
    (ProEtale.VaryingRing.ordinaryScalarMap
      (systemR l E) (baseRing l E) (scalarMap l E) X n)
    (constantRingIso (baseRing l E) j) (constantRingIso (systemR l E n) j)
    (proEtaleConstantInverseImageMap_naturality j (scalarMap l E n)).symm)
    ((ProEtale.VaryingRing.eval (systemR l E) (systemQ l E) X n).obj N)
  have h1' := congr_app h1 N
  dsimp only [TwoSquare.natTrans, TwoSquare.mk] at h1' h2 h3 h4 ⊢
  rw [h1']
  have h2' : (mateEquiv (ProEtale.VaryingRing.scalarTowerAdj (baseRing l E) j)
      (proEtaleRingModuleAdjunction j (coefficients (baseRing l E) Y)
        (coefficients (baseRing l E) X) (constantRingIso (baseRing l E) j))
      (TwoSquare.mk _ _ _ _ (eqToIso (evaluationPullback (baseRing l E) j n)).inv)).app
        ((systemRestriction l E X).obj N) = 𝟙 _ := h2
  have hL := congrArg (fun z ↦
    ((evaluation ℕᵒᵖ (Modules (baseRing l E) Y)).obj (op n)).map
      ((systemProperOrdinary l E j).hom.app N) ≫ z ≫
        (moduleDirectImage (baseRing l E) j).map
          ((canonicalEvaluation l E X n).hom.app N)) h2'
  dsimp only [Functor.id_obj, Functor.comp_obj] at hL
  erw [Category.id_comp] at hL
  have hR := congrArg₂ (fun x y ↦
    (canonicalEvaluation l E Y n).hom.app
      ((ProEtale.VaryingRing.push (systemR l E) (systemQ l E) j).obj N) ≫
        (SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
          (systemR l E) (baseRing l E) (scalarMap l E) Y n)).map x ≫ y) h3 h4
  exact hL.trans ((systemProperEvaluationCube l E j n N).trans hR.symm)

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem finiteOpenModel_eq {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)) =
      PurCompactSupport.finiteOpenIso l E n j := by
  exact (PurCompactSupport.finiteOpen_native l E n j).symm

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem ordinaryOpenCube {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) (M : coefficientSequenceModules.{u, u} l E X) :
    ((evaluation ℕᵒᵖ (Modules (baseRing l E) Y)).obj (op n)).map
        ((asIso (systemOpenMap l E j)).inv.app M) ≫
      (moduleJ (baseRing l E) j).map ((canonicalEvaluation l E X n).hom.app M) ≫
      (PurCompactSupport.openRestrictionMap
        (constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)) j).app
        ((coefficientSequenceEvaluation l E X n).obj M) =
    (canonicalEvaluation l E Y n).hom.app
        ((ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j).obj M) ≫
      (SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
        (systemR l E) (baseRing l E) (scalarMap l E) Y n)).map
        ((nativeOpenEval l E j n).hom.app M) := by
  let EX := (evaluation ℕᵒᵖ (Modules (baseRing l E) X)).obj (op n)
  let EY := (evaluation ℕᵒᵖ (Modules (baseRing l E) Y)).obj (op n)
  let rX := SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
    (systemR l E) (baseRing l E) (scalarMap l E) X n)
  let rY := SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
    (systemR l E) (baseRing l E) (scalarMap l E) Y n)
  let em : ProEtale.VaryingRing.pull (systemR l E) (systemQ l E) j ⋙
      systemRestriction l E X ⋙ EX ≅
      (systemRestriction l E Y ⋙ EY) ⋙ modulePullback (baseRing l E) j :=
    Functor.isoWhiskerRight (asIso (systemPullMap l E j)).symm EX ≪≫
      Functor.isoWhiskerLeft (systemRestriction l E Y)
        (eqToIso (evaluationPullback (baseRing l E) j n))
  let dm : ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j ⋙
      systemRestriction l E Y ⋙ EY ≅
      (systemRestriction l E X ⋙ EX) ⋙ moduleJ (baseRing l E) j :=
    Functor.isoWhiskerRight (asIso (systemOpenMap l E j)).symm EY
  symm
  apply horizontalOpenMate
    (ProEtale.VaryingRing.moduleJAdj (systemR l E) (systemQ l E) j)
    (moduleJAdj (baseRing l E) j) (moduleJAdj (systemR l E n) j)
    (systemRestriction l E X ⋙ EX) (coefficientSequenceEvaluation l E X n)
    (systemRestriction l E Y ⋙ EY) (coefficientSequenceEvaluation l E Y n)
    rX rY em (ProEtale.VaryingRing.moduleEvalG (systemR l E) (systemQ l E) j n)
    dm (nativeOpenEval l E j n)
    (canonicalEvaluation l E X n).hom (canonicalEvaluation l E Y n).hom
    (pullSquare l E j n)
    (PurCompactSupport.openRestrictionMap
      (constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)) j)
    ?_ (nativeOpenEval_unit l E j n) ?_ ?_ M
  · intro N
    haveI : IsIso ((mateEquiv
        (ProEtale.VaryingRing.moduleJAdj (systemR l E) (systemQ l E) j)
        (ProEtale.VaryingRing.scalarTowerOpenAdj (baseRing l E) j)).symm
      (asIso (systemPullMap l E j)).symm.hom).natTrans := by
      change IsIso (systemOpenMap l E j)
      exact systemOpenMap_isIso l E j
    have h := congrArg (fun t ↦ t.app (op n))
      (inverseMate_unit
        (ProEtale.VaryingRing.moduleJAdj (systemR l E) (systemQ l E) j)
        (ProEtale.VaryingRing.scalarTowerOpenAdj (baseRing l E) j)
        (systemRestriction l E X) (systemRestriction l E Y)
        (asIso (systemPullMap l E j)).symm N)
    change (((systemRestriction l E X).map
        ((ProEtale.VaryingRing.moduleJAdj (systemR l E) (systemQ l E) j).unit.app N)).app
          (op n)) ≫
      ((((inv (systemPullMap l E j)).app
        ((ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j).obj N)).app
          (op n)) ≫ 𝟙 _) ≫
      (((towerPullback (baseRing l E) j).map
        ((inv (systemOpenMap l E j)).app N)).app (op n)) =
      (((ProEtale.VaryingRing.scalarTowerOpenAdj (baseRing l E) j).unit.app
        ((systemRestriction l E X).obj N)).app (op n))
    rw [Category.comp_id]
    exact h
  · intro N
    have h := canonicalPullCube l E j n N
    have h' := congrArg (fun z ↦
      EX.map ((asIso (systemPullMap l E j)).inv.app N) ≫
        (eqToIso (evaluationPullback (baseRing l E) j n)).hom.app
          ((systemRestriction l E Y).obj N) ≫ z ≫
        rX.map ((ProEtale.VaryingRing.moduleEvalG
          (systemR l E) (systemQ l E) j n).hom.app N)) h
    simp only [EX, rX, Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, ← Functor.map_comp, asIso_inv,
      NatIso.isIso_inv_app, IsIso.inv_hom_id, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    dsimp only [ProEtale.VaryingRing.eval, coefficientSequenceEvaluation,
      SemilinearSections.evaluation] at h' ⊢
    simpa only [em, EX, rX, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      NatIso.isIso_inv_app, IsIso.inv_hom_id, IsIso.inv_hom_id_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using h'
  · intro N
    haveI : IsIso (pullSquare l E j n) := pullSquare_isIso l E j n
    have h := unit_mateEquiv_symm
      (PurCompactSupport.openAdjunction
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) j)
      (PurCompactSupport.openAdjunction (constants l E) j)
      (TwoSquare.mk _ _ _ _ (inv (pullSquare l E j n))) N
    have h' := congrArg (fun z ↦ z ≫
      (pullSquare l E j n).app ((PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) j).obj N)) h
    simp only [Category.assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id,
      Category.comp_id] at h'
    simpa only [rX, PurCompactSupport.openRestrictionMap, pullSquare,
      PurCompactSupport.openAdjunction, moduleJAdj, moduleJ, modulePullback,
      constants, PurCompactSupport.finite, constantFiniteChange,
      ProEtale.VaryingRing.ordinaryScalarMap, nativeConstantScalarMap,
      proEtaleRingOpenExtension, baseRing, systemR, compactSupportSystemLevel,
      constantRingIso,
      sfConstantCoefficientIso, constantFiniteRingMap, RingHom.ulift,
      SemilinearSections.res, proEtaleRingRestrictScalars, TwoSquare.natTrans,
      coefficients, ProEtale.VaryingRing.coefficients,
      Functor.id_obj,
      Category.assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id,
      IsIso.inv_hom_id_assoc, Category.comp_id] using h'.symm

private instance nativeOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (nativeSystemOpen l E j).Additive := by
  change (ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j).Additive
  infer_instance

private instance nativeOpen_limits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteLimits (nativeSystemOpen l E j) := by
  change PreservesFiniteLimits
    (ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j)
  infer_instance

private instance nativeOpen_colimits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteColimits (nativeSystemOpen l E j) := by
  change PreservesFiniteColimits
    (ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j)
  infer_instance

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem nativeEval_localize {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    letI := nativeLevelOpen_additive l E j n
    letI := nativeLevelOpen_limits l E j n
    letI := nativeLevelOpen_colimits l E j n
    ProEtale.VaryingRing.evalJ (systemR l E) (systemQ l E) j n =
      Functor.mapDerivedCategorySquareIso (nativeOpenEval l E j n) := by
  haveI := nativeLevelOpen_additive l E j n
  haveI := nativeLevelOpen_limits l E j n
  haveI := nativeLevelOpen_colimits l E j n
  haveI := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  haveI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  haveI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  haveI := nativeEvaluation_additive l E X n
  haveI := nativeEvaluation_additive l E Y n
  haveI := nativeEvaluation_limits l E X n
  haveI := nativeEvaluation_limits l E Y n
  haveI := nativeEvaluation_colimits l E X n
  haveI := nativeEvaluation_colimits l E Y n
  have h := nativeOpenEvaluation_localize l E j n
  erw [compactSupportNativeOpenEvaluation, compactSupportOrdinaryOpenEvaluation,
    square_postcompose _ _ _ _ _ (nativeOpenEval l E j n)
      (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))] at h
  apply Iso.ext
  ext M
  apply (cancel_mono ((Functor.mapDerivedCategoryNatIso
    (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))).hom.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj M))).1
  exact congr_app (congrArg Iso.hom h) M

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem derivedCanonicalOpenCube {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived.{u, u} l E X) :
    (ev (baseRing l E) Y n).map ((systemOpen l E j).inv.app N) ≫
      (evalJ (baseRing l E) j n).hom.app ((systemU l E X).obj N) ≫
      (moduleJ (baseRing l E) j).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E X n)).hom.app N) ≫
      (PurCompactSupport.openRestriction
        (constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)) j).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj N) =
    (Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E Y n)).hom.app
        ((ProEtale.VaryingRing.J (systemR l E) (systemQ l E) j).obj N) ≫
      (SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
        (systemR l E) (baseRing l E) (scalarMap l E) Y n)).mapDerivedCategory.map
        ((ProEtale.VaryingRing.evalJ (systemR l E) (systemQ l E) j n).hom.app N) := by
  let a := constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)
  let c := asIso (PurCompactSupport.openRestrictionMap a j)
  haveI := nativeEvaluation_additive l E X n
  haveI := nativeEvaluation_additive l E Y n
  haveI := coefficientSequenceEvaluation_additive l E X n
  haveI := coefficientSequenceEvaluation_additive l E Y n
  haveI := coefficientSequenceEvaluation_limits l E X n
  haveI := coefficientSequenceEvaluation_limits l E Y n
  haveI := coefficientSequenceEvaluation_colimits l E X n
  haveI := coefficientSequenceEvaluation_colimits l E Y n
  haveI := nativeEvaluation_limits l E X n
  haveI := nativeEvaluation_limits l E Y n
  haveI := nativeEvaluation_colimits l E X n
  haveI := nativeEvaluation_colimits l E Y n
  haveI := nativeLevelOpen_additive l E j n
  haveI := nativeLevelOpen_limits l E j n
  haveI := nativeLevelOpen_colimits l E j n
  haveI := moduleJ_additive (systemR l E n) j
  haveI := moduleJ_finiteLimits (systemR l E n) j
  haveI := moduleJ_finiteColimits (systemR l E n) j
  haveI := SemilinearSections.resLimits (a.map X)
  haveI := SemilinearSections.resColimits (a.map X)
  haveI := SemilinearSections.resLimits (a.map Y)
  haveI := SemilinearSections.resColimits (a.map Y)
  have h := Functor.mapDerivedCategory_exactCube
    (ProEtale.VaryingRing.extension (systemR l E) (systemQ l E) j)
    (systemRestriction l E Y)
    ((evaluation ℕᵒᵖ (Modules (baseRing l E) Y)).obj (op n))
    (systemRestriction l E X) (towerJ (baseRing l E) j)
    ((evaluation ℕᵒᵖ (Modules (baseRing l E) X)).obj (op n))
    (moduleJ (baseRing l E) j)
    (coefficientSequenceEvaluation l E X n) (SemilinearSections.res (a.map X))
    (coefficientSequenceEvaluation l E Y n)
    (SemilinearSections.res (a.map Y)) (moduleJ (systemR l E n) j)
    (asIso (systemOpenMap l E j)).symm (Iso.refl _)
    (canonicalEvaluation l E X n) (canonicalEvaluation l E Y n)
    (nativeOpenEval l E j n) c.symm (by
      intro M
      simp only [Iso.refl_hom, Iso.symm_hom, NatTrans.id_app]
      erw [Category.id_comp]
      apply (cancel_mono (c.hom.app
        ((coefficientSequenceEvaluation l E X n).obj M))).1
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app, Category.comp_id]
      have hOrd := ordinaryOpenCube l E j n M
      dsimp only [c, a, ProEtale.VaryingRing.ordinaryScalarMap, scalarMap,
        nativeConstantScalarMap, constantFiniteChange, constantFiniteRingMap,
        RingHom.ulift] at hOrd ⊢
      exact hOrd)
  have hn := congr_app h N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn
  change (ev (baseRing l E) Y n).map
      ((Functor.mapDerivedCategorySquareIso
        (asIso (systemOpenMap l E j)).symm).hom.app N) ≫
    (Functor.mapDerivedCategorySquareIso
      (F₁ := towerJ (baseRing l E) j)
      (F₂ := (evaluation ℕᵒᵖ (Modules (baseRing l E) Y)).obj (op n))
      (G₁ := (evaluation ℕᵒᵖ (Modules (baseRing l E) X)).obj (op n))
      (G₂ := moduleJ (baseRing l E) j) (Iso.refl _)).hom.app
      ((systemU l E X).obj N) ≫
    (moduleJ (baseRing l E) j).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E X n)).hom.app N) =
    (Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E Y n)).hom.app
      ((ProEtale.VaryingRing.J (systemR l E) (systemQ l E) j).obj N) ≫
    (SemilinearSections.res (a.map Y)).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso (nativeOpenEval l E j n)).hom.app N) ≫
    (Functor.mapDerivedCategorySquareIso c.symm).hom.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj N) at hn
  rw [Functor.square_symm_hom, Functor.square_symm_hom] at hn
  change (ev (baseRing l E) Y n).map ((systemOpen l E j).inv.app N) ≫
      (evalJ (baseRing l E) j n).hom.app ((systemU l E X).obj N) ≫
      (moduleJ (baseRing l E) j).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E X n)).hom.app N) =
    (Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E Y n)).hom.app
        ((ProEtale.VaryingRing.J (systemR l E) (systemQ l E) j).obj N) ≫
      (SemilinearSections.res (a.map Y)).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (nativeOpenEval l E j n)).hom.app N) ≫
      (PurCompactSupport.openRestriction a j).inv.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj N) at hn
  rw [← nativeEval_localize] at hn
  apply (cancel_mono ((PurCompactSupport.openRestriction a j).inv.app
    ((coefficientSequenceDerivedEvaluation l E X n).obj N))).1
  simp only [a, Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  simpa only [a, ProEtale.VaryingRing.ordinaryScalarMap, scalarMap,
    nativeConstantScalarMap, constantFiniteChange, constantFiniteRingMap,
    RingHom.ulift] using hn

set_option maxHeartbeats 2000000 in
-- Comparing the native and ringed-site coordinates expands the sectionwise models.
private theorem canonicalEvaluation_localize (W : Scheme.{u}) (n : ℕ) :
    Functor.mapDerivedCategorySquareIso (canonicalEvaluation l E W n) =
      evaluationRestriction l E W n ≪≫
        Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E W n)
          (positiveRestrictionIdentification l E W (n + 1) (Nat.le_add_left 1 n)) := by
  haveI := nativeEvaluation_additive l E W n
  haveI := nativeEvaluation_limits l E W n
  haveI := nativeEvaluation_colimits l E W n
  haveI := finiteRestriction_additive l E W n
  haveI := finiteRestriction_limits l E W n
  haveI := finiteRestriction_colimits l E W n
  haveI := SemilinearSections.resLimits (ProEtale.VaryingRing.ordinaryScalarMap
    (systemR l E) (baseRing l E) (scalarMap l E) W n)
  haveI := SemilinearSections.resColimits (ProEtale.VaryingRing.ordinaryScalarMap
    (systemR l E) (baseRing l E) (scalarMap l E) W n)
  erw [canonicalEvaluation, square_postcompose _ _ _ _ _
    (evaluationRestrictionOrdinary l E W n) (ordinaryIdentification l E W n),
    ordinaryIdentification_localize]
  rfl

set_option maxHeartbeats 2000000 in
-- Normalize the two section-site presentations before the final derived cancellation.
/-- Open evaluation commutes with restriction from the native system to constants.
Source: Stacks 03DI, 0E8I, 0940; the open square in the proof of
lem-pur-native-support-finite-evaluation.
(blueprint: lem-pur-native-open-finite-evaluation).
Proof: transpose the ordinary open restriction comparisons under their specified
extension-by-zero/restriction adjunctions. Both transposes are the same map:
on the open it is the identity on sections, with coefficient action identified by
the quotient square; off the open both extensions are zero. The open adjunction
units and triangle identities therefore identify these actual comparisons, rather
than merely exhibiting some isomorphism. Evaluate this ordinary commuting cube
and apply exact localization, whose composition comparisons preserve pasting.
The adjoint-uniqueness finiteOpenIso and compactSupportOpenModel preserve the
same units, so they give precisely nativeFiniteOpen. Transport the outer scalar
restrictions by positiveRestrictionIdentification; cancel its adjacent inverse
pairs. This gives the equality, including the empty open and exponent one. -/
theorem nativeOpen_finiteEvaluation_legacy
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ)
    (N : coefficientSequenceDerived.{u, u} l E X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((systemOpen l E j).inv.app N) ≫
      (evalJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j n).hom.app
        ((systemU l E X).obj N) ≫
      (moduleJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        j).mapDerivedCategory.map ((evaluationRestriction l E X n).hom.app N) ≫
      (finiteOpenRestriction l E j n).hom.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N) =
    (evaluationRestriction l E Y n).hom.app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj N) ≫
      (finiteRestriction l E Y n).map ((nativeFiniteOpen l E j n).hom.app N) := by
  have h := derivedCanonicalOpenCube l E j n N
  rw [canonicalEvaluation_localize, canonicalEvaluation_localize] at h
  apply (cancel_mono
    ((positiveRestrictionIdentification l E Y (n + 1) (Nat.le_add_left 1 n)).hom.app
      (((coefficientSequenceDerivedEvaluation l E X n) ⋙
        (PurCompactSupport.openExtension
          (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n))
          j).mapDerivedCategory).obj N))).1
  simp only [finiteOpenRestriction, nativeFiniteOpen, finiteOpenModel_eq, finiteRestriction,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]
  have hn := (positiveRestrictionIdentification l E Y
    (n + 1) (Nat.le_add_left 1 n)).hom.naturality
      ((ProEtale.VaryingRing.evalJ (systemR l E) (systemQ l E) j n).hom.app N)
  simp only [Functor.comp_obj, Category.comp_id, Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_app]
  erw [hn]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Functor.comp_obj, Category.assoc] at h
  dsimp only [constants, PurCompactSupport.finite, proEtaleRingOpenExtension, moduleJ,
    modulePullback, pbcDerivedRestrict, pbcRestrict, SemilinearSections.res,
    proEtaleRingRestrictScalars, constantRingIso, sfConstantCoefficientIso,
    baseRing, systemR, systemQ, ProEtale.VaryingRing.ordinaryScalarMap, scalarMap,
    nativeConstantScalarMap, constantFiniteChange, constantFiniteRingMap,
    RingHom.ulift, coefficientSequenceDerivedEvaluation, ProEtale.VaryingRing.ev,
    ProEtale.VaryingRing.eval, coefficientSequenceEvaluation,
    SemilinearSections.evaluation] at h ⊢
  exact h

end WeilConjectures.PurStrictScalar
