/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q128, N2
-/
module

public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import WeilConjectures.Compactification.BaseChange

public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.CompleteCompactSupportProetale
import Sheaf.Paper.CompletedOpenEndpointLimitTransport
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import all Sheaf.CategoryTheory.StrictRoosShiftLocalization
import all Sheaf.Paper.NormalizedLimitSquareCoherence
import all Sheaf.Paper.ExactProductFunctorStrictLimit
import all Sheaf.Paper.StrictTowerExchangeMateNormalization
import all Sheaf.Paper.RingedOpenScalarLimitCoherence
import Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
import Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.RingedOpenScalarAdjunction
import all Sheaf.Paper.OpenImmersionTensorPiece
import all Sheaf.Paper.RelativeCompactSupportPasting
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
import all Sheaf.AlgebraicGeometry.ProEtaleRingRestrictionSquare

/-!
# Canonical comparisons for strict-tower realization

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
Definition 1939 and the proof of thm-cbc-complete-proetale; Stacks 03DI, 09BP, 0A07
(blueprint: def-cbc-strict-tower-realization-comparisons).

All comparisons below are adjunction mates or their exact derived transports.
The strict composite is constructed before applying either Rlim or evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Finish proof checking before the final axiom scan.
set_option Elab.async false
-- Avoid repeatedly traversing the large dependent normalized-comparison interfaces.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.StrictTower
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory proEtaleRingModulePullback proEtaleRingModuleAdjunction

attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Pointwise preservation transferred to the finite-limit class.
Source: Mathlib functor-category limits
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
instance cbcRealizationWhiskerLimits {C : Type uC} {D : Type uD} [Category.{vC} C]
    [Category.{vD} D] [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Pointwise preservation transferred to the finite-colimit class.
Source: Mathlib functor-category colimits
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
instance cbcRealizationWhiskerColimits {C : Type uC} {D : Type uD} [Category.{vC} C]
    [Category.{vD} D] [HasFiniteColimits C] (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- Constant-tower/Rlim adjunction for an arbitrary coefficient sheaf.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitAdj (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _).mapDerivedCategory ⊣ completedRlim T R :=
  (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣
    completedTowerLimit T R).mapDerivedCategoryRightDerivedAdjunction

/-- Exact transport of the identity constant-diagram comparison.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationConst {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical limit comparison, defined by the constant-diagram mate.
This definition fixes its value on resolutions and on strict augmentations.
Source: Stacks 09BP, 0A07
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitMap {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    completedRlim T R ⋙ F.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory ⋙ completedRlim S R' :=
  mateEquiv (cbcRealizationLimitAdj T R) (cbcRealizationLimitAdj S R')
    (cbcRealizationConst F).hom

section LimitMateNormalization

-- Unit-normalized Roos comparison, following the existing endpoint proof
-- (Stacks 09BP, 0941; lem-cbc-completed-open-endpoint-limit-transport).
private def cbcRealizationCochainUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  derivedCochainRightUnit (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)

private theorem cbcRealizationCochainUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (X : CochainComplex (ℕᵒᵖ ⥤ reductionModules T R) ℤ) :
    (cbcRealizationCochainUnit T R).app X = exchangeDerivedUnit (completedTowerLimit T R) X := by
  unfold cbcRealizationCochainUnit
  rw [cochainRightUnit_app_eq]
  dsimp only [exchangeDerivedUnit]
  simp only [quotient_hom_id, quotient_inv_id, Category.id_comp]
  erw [(completedTowerLimit T R).rightDerivedFunctor.map_id, Category.comp_id]
  rfl

private def cbcRealizationRoosUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedRlim T R :=
  (Functor.isoWhiskerRight
    (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
    DerivedCategory.Q).inv ≫ cbcRealizationCochainUnit T R

private theorem cbcRealizationRoosUnit_derived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedRlim T R).IsRightDerivedFunctor (cbcRealizationRoosUnit T R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ reductionModules T R) (.up ℤ)) := by
  have : (completedRlim T R).IsRightDerivedFunctor (completedRlimUnit T R)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    dsimp only [completedRlim, completedRlimUnit]
    infer_instance
  have h := cochainRightUnit_universal (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).mpr
  exact (Functor.isLeftKanExtension_iff_of_iso₂
    (cbcRealizationCochainUnit T R) (cbcRealizationRoosUnit T R)
    (Functor.isoWhiskerRight
      (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
      DerivedCategory.Q) (Iso.refl _) (by
        dsimp only [cbcRealizationRoosUnit, Iso.refl_hom]
        rw [Functor.whiskerLeft_id', Category.comp_id,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp])).mp h

private theorem cbcRealizationRoos_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (LA : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory C)
    (LB : DerivedCategory (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory D)
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
    (hnorm : CbcLimitNormalized F LA LB
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ∀ X : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      F.mapDerivedCategory.map (uA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso F (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        uB.app ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex
          (.up ℤ)).obj X) := by
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  intro X
  let Y :=
    (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj X
  let iA := CategoryTheory.StrictRoosShiftProof.limitModelPointIso X
  let iB := CategoryTheory.StrictRoosShiftProof.limitModelPointIso Y
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  have hi : (F.mapHomologicalComplex (.up ℤ)).map iA.hom ≫ beta =
      (NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom := by
    apply limit.hom_ext
    intro n
    dsimp only [beta]
    rw [Category.assoc, limit.lift_π]
    dsimp only [Functor.mapCone, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [← Functor.map_comp,
      CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π,
      Category.assoc, CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π]
    apply HomologicalComplex.Hom.ext
    funext q
    change F.map (limit.π (X.X q) n) =
      (preservesLimitIso F (X.X q)).hom ≫ limit.π _ n
    exact (preservesLimitIso_hom_π F (X.X q) n).symm
  have hh := congrArg (fun z ↦ F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫ z)
    (hnorm.equation X)
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc, Functor.map_comp] at hh
  change F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫
    F.mapDerivedCategory.map (DerivedCategory.Q.map iA.inv) ≫ _ = _ at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc] at hh
  simp only [← DerivedCategory.Q.map_comp_assoc] at hh
  erw [reassoc_of% hi] at hh
  change _ = _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom ≫ iB.inv) ≫ _ at hh
  simp only [Iso.hom_inv_id, Category.comp_id] at hh
  exact hh

private theorem cbcRealizationLimit_cochain_normalized
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hA : ∀ X, uA.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ C) ⥤ C) X)
    (hB : ∀ X, uB.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ D) ⥤ D) X)
    (lambda : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hnorm : CbcLimitNormalized F
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ExchangeDerivedPushNormalized (lim : (ℕᵒᵖ ⥤ C) ⥤ C)
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D) F ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      (preservesLimitNatIso F (J := ℕᵒᵖ)) lambda := by
  have h := cbcRealizationRoos_normalization F
    (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
    (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor uA uB lambda hnorm
  intro X
  simpa only [hA, hB] using h X

-- Check the ordinary constant/limit mate before specializing coefficient categories.
private theorem cbcRealizationOrdinaryLimitMate
    {C D : Type*} [Category C] [Category D] [HasLimits C] [HasLimits D]
    (F : C ⥤ D) [PreservesLimitsOfShape ℕᵒᵖ F] :
    (mateEquiv (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
      (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
      (TwoSquare.mk _ _ _ _ (Functor.compConstIso ℕᵒᵖ F).hom)).natTrans =
        (preservesLimitNatIso F (J := ℕᵒᵖ)).hom := by
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  have h := congrArg (fun z ↦ z.app n)
    (mateEquiv_counit aa bb (TwoSquare.mk _ _ _ _
      (Functor.compConstIso ℕᵒᵖ F).hom) M)
  change (mateEquiv aa bb (TwoSquare.mk _ _ _ _
    (Functor.compConstIso ℕᵒᵖ F).hom)).natTrans.app M ≫ limit.π _ n = _ at h
  change _ = 𝟙 _ ≫ F.map (limit.π M n) at h
  rw [Category.id_comp] at h
  exact h.trans (preservesLimitIso_hom_π F M n).symm

private theorem cbcRealizationLimit_mate_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hphi : ∀ N : ℕ → C, IsIso (piComparison F N))
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hA : ∀ X, uA.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ C) ⥤ C) X)
    (hB : ∀ X, uB.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ D) ⥤ D) X)
    (lambda : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hnorm : CbcLimitNormalized F
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    lambda.hom =
      mateEquiv
        (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        ((Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm ≪≫
          Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
          Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ)
            ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)).hom := by
  have : PreservesLimitsOfShape (Discrete ℕ) F := natProducts F hphi
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  have hm := cbcRealizationOrdinaryLimitMate F
  have he := cbcRealizationLimit_cochain_normalized F uA uB hA hB lambda hnorm
  have hh := exactDerivedMate_eq aa bb (Functor.compConstIso ℕᵒᵖ F) tau hm lambda he
  simpa only [exactDerivedMate, Functor.mapDerivedCategorySquareIso] using hh

/-- The specified mate is invertible for an exact product-preserving functor.
Source: Stacks 09BP and the normalized strict-limit lemma
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: apply lem-cbc-exact-product-functor-strict-limit. Its signed Roos formula
is induced by the canonical product map. On a K-injective tower it is the ordinary
limit comparison followed by a target resolution; adjunction transposition shows
that this is exactly cbcRealizationLimitMap. The normalized comparison is invertible,
and its augmentation equation also identifies the constant-diagram mate. -/
theorem cbcRealizationLimitMap_isIso {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_products : ∀ M : ℕ → reductionModules T R, IsIso (piComparison F M)) :
    IsIso (cbcRealizationLimitMap F) := by
  have := ambient_exact T R
  have := ambient_exact S R'
  let a := Classical.choose (CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology T) (reductionModuleRing T R) (completedRlim T R) (cbcRealizationRoosUnit T R)
      (cbcRealizationRoosUnit_derived T R))
  let b := Classical.choose (CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology S) (reductionModuleRing S R') (completedRlim S R') (cbcRealizationRoosUnit S R')
      (cbcRealizationRoosUnit_derived S R'))
  let c := Classical.choose (CategoryTheory.NormalizedLimitSquare.comparisonData a b F _products)
  have hnorm := CategoryTheory.comparison_normalized F a b c
  have hm := cbcRealizationLimit_mate_eq F _products
    (cbcRealizationCochainUnit T R) (cbcRealizationCochainUnit S R')
    (cbcRealizationCochainUnit_eq T R) (cbcRealizationCochainUnit_eq S R') c.lambda hnorm
  change c.lambda.hom = cbcRealizationLimitMap F at hm
  rw [← hm]
  infer_instance

end LimitMateNormalization

attribute [local irreducible] limit

/-- Restriction of the scalar action on the ordinary module category.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationRes (T : Scheme.{t}) :=
  proEtaleRingRestrictScalars (exchangeScalar d T)

/-- The recorded open extension adjunction transported by the section-normalized map.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⊣
      proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) :=
  Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
    (@asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)).symm

/-- Termwise completed open extension on strict towers, retaining every transition.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationTowerJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcOpenShriek d j inferInstance)

/-- The exact derived open functor on completed strict towers.
Source: Stacks 03DJ (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRealizationTowerJ d j).mapDerivedCategory

/-- Derived adjunction on completed towers with the normalized open unit.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⊣ d.towerPull j :=
  Adjunction.ofNatIsoRight
    ((cbcRealizationOpenAdj d j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (d.towerModulePull j).rightDerivedFunctorIsoMapDerivedCategory

/-- The inverse tensor/open comparison is the transpose of the reduced open unit.
It is one strict-tower map, not a family of maps in separate derived categories.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReductionInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) ⟶
      (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) :=
  ((cbcRealizationTowerAdj d j).homEquiv _ _).symm
    ((completedReductionTower U d).map ((cbcDerivedOpenAdjunction d j).unit.app K) ≫
      (d.reductionTowerPullbackIso j).inv.app
        ((cbcDerivedOpenShriek d j inferInstance).obj K))

private theorem cbcTranspose_leftAdjointUniq
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R)
    {J J' : E ⥤ H} {S : H ⥤ E} (b : J ⊣ S) (b' : J' ⊣ S)
    (U : C ⥤ E) (V : D ⥤ H) (e : V ⋙ S ≅ R ⋙ U) (K : C) :
    (b.leftAdjointUniq b').hom.app (U.obj K) ≫
        (b'.homEquiv _ _).symm (U.map (a'.unit.app K) ≫ e.inv.app (L'.obj K)) =
      (b.homEquiv _ _).symm (U.map (a.unit.app K) ≫ e.inv.app (L.obj K)) ≫
        V.map ((a.leftAdjointUniq a').hom.app K) := by
  apply (b.homEquiv _ _).injective
  have hleft : ∀ f : J'.obj (U.obj K) ⟶ V.obj (L'.obj K),
      b.homEquiv _ _ ((b.leftAdjointUniq b').hom.app (U.obj K) ≫ f) =
        b'.homEquiv _ _ f := by
    intro f
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app]
  rw [hleft]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  conv_rhs => rw [b.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply]
  have hn := e.inv.naturality ((a.leftAdjointUniq a').hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← U.map_comp,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- The tensor/open transpose is natural and invertible.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: naturality is naturality of the open unit and of the strict reduction/pullback
comparison. On K-flat representatives its evaluation is the sheafified balancing map
j_!(Q) tensor P_n to j_!(Q tensor j^*P_n). Extension preserves K-flatness: tensor
with an acyclic ambient complex is extension of tensor with its exact restriction.
The inverse balancing maps commute with differentials and all quotient transitions.
Thus the inverse exists in the derived category of strict towers itself. -/
theorem cbcRealizationReductionInv_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (∀ K : d.derived U, IsIso (cbcRealizationReductionInv d j K)) ∧
      ∀ (K L : d.derived U) (k : K ⟶ L),
        (cbcRealizationJ d j).map ((completedReductionTower U d).map k) ≫
            cbcRealizationReductionInv d j L =
          cbcRealizationReductionInv d j K ≫
            (completedReductionTower T d).map
              ((cbcDerivedOpenShriek d j inferInstance).map k) := by
  let a := cbcDerivedOpenAdjunction d j
  let a' := cbcEndpointDerivedOpenAdj d j
  let b := cbcRealizationTowerAdj d j
  let b' := cbcEndpointTowerOpenAdj d j
  have h := cbcTranspose_leftAdjointUniq a a' b b'
    (completedReductionTower U d) (completedReductionTower T d)
    (d.reductionTowerPullbackIso j)
  constructor
  · intro K
    have hh := h K
    change (b.leftAdjointUniq b').hom.app ((completedReductionTower U d).obj K) ≫
        cbcEndpointReductionInv d j K =
      cbcRealizationReductionInv d j K ≫
        (completedReductionTower T d).map ((a.leftAdjointUniq a').hom.app K) at hh
    have : IsIso (cbcEndpointReductionInv d j K) :=
      (cbcEndpointReductionInv_properties d j).1 K
    have : IsIso (cbcRealizationReductionInv d j K ≫
        (completedReductionTower T d).map ((a.leftAdjointUniq a').hom.app K)) := by
      rw [← hh]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((completedReductionTower T d).map
      ((a.leftAdjointUniq a').hom.app K))
  · intro K L k
    apply ((cbcRealizationTowerAdj d j).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [cbcRealizationReductionInv, Equiv.apply_symm_apply]
    have hu := (cbcDerivedOpenAdjunction d j).unit.naturality k
    dsimp only [Functor.comp_map, Functor.id_map] at hu
    have he := (d.reductionTowerPullbackIso j).inv.naturality
      ((cbcDerivedOpenShriek d j inferInstance).map k)
    dsimp only [Functor.comp_map] at he
    rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, he]
    simp only [Category.assoc]

/-- The canonical tensor comparison on the full strict quotient tower.
Source: Stacks 0E8I (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReduction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) ≅
      (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) :=
  (@asIso _ _ _ _ (cbcRealizationReductionInv d j K)
    ((cbcRealizationReductionInv_properties d j).1 K)).symm

/-- Scalar restriction/open extension comparison, defined by the pullback mate.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpenInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j ⟶
      cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T :=
  (mateEquiv (cbcRealizationOpenAdj d j) (ProEtale.StrictTower.moduleJAdj A j)).symm
    (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))
      (proEtaleRingRestrictionPullbackInv_isIso j
        (exchangeConstantRing T A) (d.completedRing T)
        (exchangeConstantRing U A) (d.completedRing U)
        (exchangeScalar d T) (exchangeScalar d U)
        (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))).inv

section ScalarOpenInvertibility

attribute [local irreducible] cbcRealizationOpenAdj

/-- The scalar/open mate is invertible and preserves the normalized open adjunction.
Source: Stacks 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: the extension presheaf has the same direct-sum summands and restriction maps
after scalar restriction. Its action is the completed action composed with the scalar
map. Sheafification therefore gives the identity on the underlying additive sheaf.
The open unit includes the structure-map summand and the counit evaluates that
summand; both are unchanged. Its transpose is the displayed mate, so it is invertible. -/
theorem cbcRealizationScalarOpenInv_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcRealizationScalarOpenInv d j) := by
  let R := exchangeConstantRing T A
  let S := d.completedRing T
  let adjS := Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j S (d.completedRing U) (d.integralRingIso j))
  let adjR := ProEtale.StrictTower.moduleJAdj A j
  let e := (cbcRealizationOpenAdj d j).leftAdjointUniq adjS
  obtain ⟨eS, ⟨hS⟩⟩ := proEtaleOpen_slicePresentation j
    S (d.completedRing U) (d.integralRingIso j)
  obtain ⟨eR, ⟨hR⟩⟩ := proEtaleOpen_slicePresentation j
    R (exchangeConstantRing U A) (exchangeConstantIso j A)
  let := SheafOfModules.localizedUnit_isIso j S
  let := SheafOfModules.localizedUnit_isIso j R
  let ffS := (SheafOfModules.localizedModuleAdjunctionIndependent
    S (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  let ffR := (SheafOfModules.localizedModuleAdjunctionIndependent
    R (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  have := ffS.full
  have := ffS.faithful
  have := ffR.full
  have := ffR.faithful
  have : (cbcOpenShriek d j inferInstance).Full := Functor.Full.of_iso (e ≪≫ hS).symm
  have : (cbcOpenShriek d j inferInstance).Faithful :=
    Functor.Faithful.of_iso (e ≪≫ hS).symm
  have : (moduleJ A j).Full := Functor.Full.of_iso hR.symm
  have : (moduleJ A j).Faithful := Functor.Faithful.of_iso hR.symm
  have : IsIso (cbcRealizationOpenAdj d j).unit := inferInstance
  obtain ⟨_, _, scalarIso, _, _⟩ :=
    SheafOfModules.RingedOpenScalar.comparison.{t + 1, t, 0, t + 2}
      (ProEt.mk j) (exchangeScalar d T)
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let LR := SheafOfModules.localizedModuleExtension.{t} R (ProEt.mk j)
  have hs : LR.essImage
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M)) := by
    exact ⟨(SheafOfModules.RingedOpenScalar.sliceScalars.{t + 1, t, 0}
      (ProEt.mk j) (exchangeScalar d T)).obj (eS.functor.obj M),
      ⟨(scalarIso.app (eS.functor.obj M)).symm ≪≫
        (cbcRealizationRes d T).mapIso ((e ≪≫ hS).app M).symm⟩⟩
  have ht : (eR.functor ⋙ LR).essImage
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M)) :=
    Functor.essImage_comp_apply_of_essSurj.mpr hs
  have : IsIso (adjR.counit.app
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M))) :=
    adjR.isIso_counit_app_iff_mem_essImage.mpr (Functor.essImage.ofNatIso hR.symm ht)
  change IsIso (((mateEquiv (cbcRealizationOpenAdj d j) adjR).symm _).natTrans.app M)
  simp only [mateEquiv_symm_apply, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp]
  have : IsIso ((proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))) :=
    proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  infer_instance

end ScalarOpenInvertibility

/-- Canonical scalar/open comparison on ordinary modules.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T ≅
      cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j :=
  (@asIso _ _ _ _ (cbcRealizationScalarOpenInv d j)
    (cbcRealizationScalarOpenInv_isIso d j)).symm

/-- Apply scalar/open comparison to a whole strict diagram, then derive exactly.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⋙ exchangeTowerRes d T ≅
      exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d j) ≪≫
        (Functor.whiskeringRightObjCompIso _ _).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Scalar/open comparison on single derived objects, by exact descent.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationDerivedScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (cbcRealizationScalarOpen d j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The quotient/open tensor identification followed by scalar/open identification.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationQuotientOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (exchangeTowerRes d T).obj
        ((completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≅
      (ProEtale.StrictTower.J A j).obj
        ((exchangeTowerRes d U).obj ((completedReductionTower U d).obj K)) :=
  (exchangeTowerRes d T).mapIso (cbcRealizationReduction d j K) ≪≫
    (cbcRealizationTowerScalarOpen d j).app ((completedReductionTower U d).obj K)

-- Keep the forgetful comparison abstract before specializing the coefficient sheaves.
private theorem cbcRealizationRestrictionForgetsProducts
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (a : R ⟶ S)
    [PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S)] :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R) := by
  let e : SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R ≅
      SheafOfModules.toSheaf.{t + 1} S :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by rfl)
  exact preservesLimitsOfShape_of_natIso e.symm

/-- Products are preserved by scalar restriction and by quasi-compact constant open extension.
Source: Stacks 03D3, 09BP
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: restriction leaves the underlying additive sheaves and all limits unchanged.
For open extension, use j!N = ker(j*N to i*i^-1j*N). Direct images preserve
products sectionwise and closed inverse image preserves products on the pro-etale
site. Kernels commute with products. These are the canonical projection maps,
including for the empty product; no qcqs hypothesis on the ambient scheme is used. -/
theorem cbcRealizationProducts (T : Scheme.{t}) :
    (∀ M : ℕ → reductionModules T (d.completedRing T),
      IsIso (piComparison (cbcRealizationRes d T) M)) ∧
      ∀ {U : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
        (M : ℕ → ProEtale.StrictTower.Modules A U),
        IsIso (piComparison (ProEtale.StrictTower.moduleJ A j) M) := by
  constructor
  · intro M
    let R := reductionModuleRing T (exchangeConstantRing T A)
    let S := reductionModuleRing T (d.completedRing T)
    let G := SheafOfModules.toSheaf.{t + 1} R
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ))
        (SheafOfModules.toSheaf.{t + 1} S) :=
      ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ)) G :=
      ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S) :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : PreservesLimitsOfShape (Discrete ℕ) G :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : ReflectsLimitsOfShape (Discrete ℕ) G :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T ⋙ G) :=
      cbcRealizationRestrictionForgetsProducts (R := R) (S := S)
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (exchangeScalar d T))
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ G
    infer_instance
  · intro U j _ _ M
    let W := ProEt.mk j
    let R := exchangeConstantRing T A
    have : IsOpenImmersion W.hom := show IsOpenImmersion j from inferInstance
    have : QuasiCompact W.hom := show QuasiCompact j from inferInstance
    let L : SheafOfModules.{t + 1} ((proEtaleModuleCoefficients R).over W) ⥤
        SheafOfModules.{t + 1} (proEtaleModuleCoefficients R) :=
      proEtaleRingedExtensionByZero W R
    have : ∀ N : ULift.{t + 1} ℕ →
        ringedSiteModules.{t + 1} ((proEtaleModuleCoefficients R).over W),
        PreservesLimit (Discrete.functor N) L := fun N ↦ by
      have := (proEtaleRingedExtensionByZero_products W R (ULift.{t + 1} ℕ) N).1
      exact PreservesProduct.of_iso_comparison L N
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ)) L :=
      preservesLimitsOfShape_of_discrete L
    have : PreservesLimitsOfShape (Discrete ℕ) L :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) L
    obtain ⟨e, ⟨h⟩⟩ := proEtaleOpen_slicePresentation j R (exchangeConstantRing U A)
      (exchangeConstantIso j A)
    have : PreservesLimitsOfShape (Discrete ℕ)
        (e.functor ⋙ SheafOfModules.localizedModuleExtension.{t} R (ProEt.mk j)) := by
      change PreservesLimitsOfShape (Discrete ℕ) (e.functor ⋙ L)
      infer_instance
    have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.StrictTower.moduleJ A j) :=
      preservesLimitsOfShape_of_natIso h.symm
    infer_instance

/-- The specified scalar-restriction/Rlim isomorphism.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResLimit (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      exchangeTowerRes d T ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (cbcRealizationRes d T))
    (cbcRealizationLimitMap_isIso _ (cbcRealizationProducts d T).1)

/-- The specified constant open-extension/Rlim isomorphism.
Source: Stacks 09BP (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenLimit (d : AdicCoefficientDatum A) {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory ≅
      ProEtale.StrictTower.J A j ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (ProEtale.StrictTower.moduleJ A j))
    (cbcRealizationLimitMap_isIso _ ((cbcRealizationProducts d T).2 j))

/-- Direct-image/Rlim comparison for constant coefficients, as the conjugate
of the identity constant-diagram/pullback comparison, including both units.
Source: Stacks 0A07 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPushLimit {U T : Scheme.{t}} (f : U ⟶ T) :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor ≅
      ProEtale.StrictTower.R A f ⋙ completedRlim T (exchangeConstantRing T A) :=
  conjugateIsoEquiv
    (((proEtaleRingModuleAdjunction f (exchangeConstantRing T A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryRightDerivedAdjunction
      ).comp (cbcRealizationLimitAdj U (exchangeConstantRing U A)))
    ((cbcRealizationLimitAdj T (exchangeConstantRing T A)).comp (ProEtale.StrictTower.adj A f))
    (cbcRealizationConst (ProEtale.StrictTower.modulePullback A f)).symm

/-- The single-object direct-image/scalar comparison, with its published universal units.
Source: Stacks 0D6E (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResPush {U T : Scheme.{t}} (f : U ⟶ T) :
    d.push f ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor :=
  proEtaleRingRestrictionDerivedDirectImage f
    (exchangeConstantRing T A) (d.completedRing T)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d T) (exchangeScalar d U)
    (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)

/-- Canonical constant-tower presentation of completed pullback.
Source: Stacks 099M and finite reduction comparison
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPullLimit {U T : Scheme.{t}} (f : U ⟶ T) (K : d.derived T) :
    (cbcRealizationRes d U).mapDerivedCategory.obj ((d.completedPull f).obj K) ≅
      (completedRlim U (exchangeConstantRing U A)).obj
        ((ProEtale.StrictTower.G A f).obj
          ((exchangeTowerRes d T).obj ((completedReductionTower T d).obj K))) :=
  (cbcRealizationResLimit d U).app
      ((d.towerPull f).obj ((completedReductionTower T d).obj K)) ≪≫
    (completedRlim U (exchangeConstantRing U A)).mapIso
      ((exchangeResPull d f).app ((completedReductionTower T d).obj K))

variable {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The actual strict-tower proper/open composite, defined before evaluation.
The proper mate is the normalization dependency's mate on constant A towers.
Source: blueprint Definition 1939 and strict normalization, final paragraph
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationStrict (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (M : ProEtale.StrictTower.Derived A X) :
    (ProEtale.StrictTower.G A g).obj
        ((ProEtale.StrictTower.R A c.g).obj ((ProEtale.StrictTower.J A c.i).obj M)) ⟶
      (ProEtale.StrictTower.R A c'.g).obj
        ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj M)) :=
  (exchangeConstantSquare (A := A) sp).exchangeTowerMate.app
      ((ProEtale.StrictTower.J A c.i).obj M) ≫
    (ProEtale.StrictTower.R A c'.g).map
      ((ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app M)

/-- Source identification: specified strict projection, scalar/limit comparison,
proper corner b, and canonical quotient/open tensor comparison, in that order.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSource (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :
    (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.completedPull g).obj
          ((d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≅
      (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.G A g).obj
          ((ProEtale.StrictTower.R A c.g).obj
            ((ProEtale.StrictTower.J A c.i).obj
              ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) :=
  ((cbcRealizationRes d Y').mapDerivedCategory).mapIso
      ((completedRlim Y' (d.completedRing Y')).mapIso
        (d.towerH (f := c.g) (f' := c'.g) (g := g) (g' := gbar)
          ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≪≫
    (cbcRealizationResLimit d Y').app _ ≪≫
    (completedRlim Y' (exchangeConstantRing Y' A)).mapIso
      ((exchangeCornerB d c.g g).app _ ≪≫
        (ProEtale.StrictTower.G A g).mapIso
          ((ProEtale.StrictTower.R A c.g).mapIso (cbcRealizationQuotientOpen d c.i K)))

/-- Target identification: inverse direct-image/limit and extension/limit maps,
followed by inverse completed-pullback, scalar/open, and scalar/direct-image maps.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTarget (c' : Compactification f') (g' : X' ⟶ X)
    [qc : QuasiCompact c'.i] (K : d.derived X) :
    (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.R A c'.g).obj
          ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj
            ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) ≅
      (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.push c'.g).obj ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).obj
          ((d.completedPull g').obj K))) :=
  ((cbcRealizationPushLimit (A := A) c'.g).app _).symm ≪≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.mapIso
      (((cbcRealizationOpenLimit d c'.i).app _).symm ≪≫
        (ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.mapIso
          (cbcRealizationPullLimit d g' K).symm ≪≫
        ((cbcRealizationDerivedScalarOpen d c'.i).app ((d.completedPull g').obj K)).symm) ≪≫
    ((cbcRealizationResPush d c'.g).app _).symm

/-- Quasi-compactness of the base-changed open follows from the supplied square.
Source: Stacks 01K5 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationOpenQC [QuasiCompact f] (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar) : QuasiCompact c'.i :=
  MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)
      (c.quasiCompact_openImmersion inferInstance)

/-- The canonical single-object pullback square, by exact descent of its module square.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleSquare {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (ProEtale.StrictTower.modulePullback A i).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A r).mapDerivedCategory ≅
      (ProEtale.StrictTower.modulePullback A p).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A k).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtale.StrictTower.moduleSquareG A k r p i h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The specified single-object proper mate. On a quotient object its scalar action
is the inherited P_n action; scalar restriction preserves its unit and counit.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleProper {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (ProEtale.StrictTower.moduleDirectImage A p).rightDerivedFunctor ⋙
        (ProEtale.StrictTower.modulePullback A i).mapDerivedCategory ⟶
      (ProEtale.StrictTower.modulePullback A k).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A r).rightDerivedFunctor :=
  mateEquiv
    (proEtaleRingModuleAdjunction p (exchangeConstantRing T A)
      (exchangeConstantRing W A) (exchangeConstantIso p A)).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleRingModuleAdjunction r (exchangeConstantRing S A)
      (exchangeConstantRing V A) (exchangeConstantIso r A)).mapDerivedCategoryRightDerivedAdjunction
    (cbcRealizationSingleSquare (A := A) k r p i h).hom

/-- The inverse-open-unit map is invertible for any Cartesian open square.
Source: Stacks 03DI, 09AE
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: identify the right adjoints by restriction on the same pulled-back test
object. Their unique left-adjoint comparison is invertible and its inverse
transposes to the pulled-back open unit. This is singleBetaInv by its definition. -/
theorem cbcRealizationSingleBeta_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (b : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ b)
    (_sq : IsPullback a j' j b) :
    IsIso (ProEtale.StrictTower.singleBetaInv A a j' j b h) := by
  exact openBetaModule_isIso A a j' j b h _sq

/-- The forward single-object open exchange, with the exact finite unit normalization.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleOpen {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (b : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ b)
    (sq : IsPullback a j' j b) :
    (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A b).mapDerivedCategory ≅
      (ProEtale.StrictTower.modulePullback A a).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (ProEtale.StrictTower.singleBetaInv A a j' j b h)
        (cbcRealizationSingleBeta_isIso (A := A) a j' j b h sq)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Evaluate the source through the specified pullback, direct-image and open comparisons.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationEvalSource (c : Compactification f) (g : Y' ⟶ Y)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :=
  (ProEtale.StrictTower.evalG A g n).hom.app
      ((ProEtale.StrictTower.R A c.g).obj ((ProEtale.StrictTower.J A c.i).obj M)) ≫
    (ProEtale.StrictTower.modulePullback A g).mapDerivedCategory.map
      ((ProEtale.StrictTower.evalR A c.g n).app ((ProEtale.StrictTower.J A c.i).obj M)) ≫
    (ProEtale.StrictTower.modulePullback A g).mapDerivedCategory.map
      ((ProEtale.StrictTower.moduleDirectImage A c.g).rightDerivedFunctor.map
        ((ProEtale.StrictTower.evalJ A c.i n).hom.app M))

/-- Evaluate the target through the specified direct-image, open and pullback comparisons.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationEvalTarget (c' : Compactification f') (g' : X' ⟶ X)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :=
  (ProEtale.StrictTower.evalR A c'.g n).app
      ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj M)) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((ProEtale.StrictTower.evalJ A c'.i n).hom.app ((ProEtale.StrictTower.G A g').obj M)) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.map
        ((ProEtale.StrictTower.evalG A g' n).hom.app M))

/-- The specified finite proper/open composite, in its scalar-restricted single-object
coordinates. For M = Res(K_bullet), n denotes the quotient P_(n+1), not a new coefficient
choice. The proper factor is the adjunction mate and the open factor the inverse-unit mate.
Source: Stacks 07A7, 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationFinite (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (N : DerivedCategory (ProEtale.StrictTower.Modules A X)) :=
  (cbcRealizationSingleProper (A := A) gbar c'.g c.g g sp.w).app
      ((ProEtale.StrictTower.moduleJ A c.i).mapDerivedCategory.obj N) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((cbcRealizationSingleOpen (A := A) g' c'.i c.i gbar sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app N)

section Evaluation
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients
  proEtaleRingDerivedPullbackFactors CochainComplex.IsAcyclicTensorKFlat
  SheafOfModules.IsFlatOnSite proEtaleRingDirectImageMap

private theorem cbcEvaluationNormalizedComp {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{t + 1}).obj RV ≅ RZ)
    (hc : c = proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
    (d : proEtaleRingModuleDirectImage h RW RZ ch ⋙
      proEtaleRingModuleDirectImage k RV RW ck ≅
        proEtaleRingModuleDirectImage (h ≫ k) RV RZ c)
    (hd : ∀ (N : proEtaleRingModules Z RZ) (U : V.ProEt)
      (m : ((proEtaleRingModuleDirectImage h RW RZ ch ⋙
        proEtaleRingModuleDirectImage k RV RW ck).obj N).val.obj (op U)),
      (d.hom.app N).val.app (op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) :
    eqToIso (congrArg (proEtaleRingModulePullback (h ≫ k) RV RZ) hc) ≪≫
        exchangeModuleComposition h k RV RW RZ ck ch =
      (Adjunction.leftAdjointCompIso (proEtaleRingModuleAdjunction k RV RW ck)
        (proEtaleRingModuleAdjunction h RW RZ ch)
        (proEtaleRingModuleAdjunction (h ≫ k) RV RZ c) d).symm := by
  subst c
  simp only [eqToIso_refl, Iso.refl_trans]
  apply (conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k RV RW ck).comp
      (proEtaleRingModuleAdjunction h RW RZ ch))
    (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch))).injective
  apply Iso.ext
  calc
    (conjugateIsoEquiv _ _
        (exchangeModuleComposition h k RV RW RZ ck ch)).hom = d.hom := by
      apply NatTrans.ext
      funext N
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext m
      exact ((exchangeModuleComposition_existsUnique h k RV RW RZ ck ch).choose_spec.1
        N U.unop m).trans (hd N U.unop m).symm
    _ = (conjugateIsoEquiv _ _
        (Adjunction.leftAdjointCompIso (proEtaleRingModuleAdjunction k RV RW ck)
          (proEtaleRingModuleAdjunction h RW RZ ch)
          (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
            (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)) d).symm).hom := by
      exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ d).symm

variable (B : Type (t + 1)) [CommRing B]
private theorem cbcEvaluationConstantComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eqToIso (congrArg (proEtaleRingModulePullback (f ≫ g)
      (coefficients B Z) (coefficients B X)) (constantRingIso_comp B f g)) ≪≫
      exchangeModuleComposition f g (coefficients B Z) (coefficients B Y)
        (coefficients B X) (constantRingIso B g) (constantRingIso B f) =
      moduleGComp B f g := by
  exact cbcEvaluationNormalizedComp f g _ _ _ _ _ _ (constantRingIso_comp B f g)
    (moduleRComp B f g) (moduleRComp_existsUnique B f g).choose_spec.1

private theorem cbcEvaluationIso_transport_square {C : Type*} [Category* C]
    {P Q P' Q' E F : C} (a : P' ≅ E) (b : Q' ≅ F)
    (hp : P = P') (hq : Q = Q') (h : P = Q) (h' : P' = Q') :
    (eqToIso hp ≪≫ a).symm ≪≫ eqToIso h ≪≫ (eqToIso hq ≪≫ b) =
      a.symm ≪≫ eqToIso h' ≪≫ b := by
  subst P'
  subst Q
  subst Q'
  simp

private theorem cbcEvaluationConstantModuleSquare {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (sq : ChosenCartesianSquare k r p i) :
    (exchangeConstantSquare (A := B) sq).exchangeModuleSquare =
      moduleSquareG B k r p i sq.w := by
  rw [moduleSquareG_eq, ← cbcEvaluationConstantComp B r i, ← cbcEvaluationConstantComp B k p]
  unfold StrictTowerRingedSquare.exchangeModuleSquare
  dsimp only [exchangeConstantSquare]
  let a := exchangeModuleComposition r i (coefficients B T) (coefficients B S)
    (coefficients B V) (constantRingIso B i) (constantRingIso B r)
  let b := exchangeModuleComposition k p (coefficients B T) (coefficients B W)
    (coefficients B V) (constantRingIso B p) (constantRingIso B k)
  have result := (cbcEvaluationIso_transport_square a b
    (congrArg (proEtaleRingModulePullback (r ≫ i) (coefficients B T) (coefficients B V))
      (constantRingIso_comp B r i))
    (congrArg (proEtaleRingModulePullback (k ≫ p) (coefficients B T) (coefficients B V))
      (constantRingIso_comp B k p))
    (congrArg (modulePullback B) sq.w.symm)
    (by
      exact ((congrArg (proEtaleRingModulePullback (r ≫ i)
        (coefficients B T) (coefficients B V)) (constantRingIso_comp B r i)).symm.trans
          ((congrArg (modulePullback B) sq.w.symm).trans
            (congrArg (proEtaleRingModulePullback (k ≫ p)
              (coefficients B T) (coefficients B V)) (constantRingIso_comp B k p)))))).symm
  dsimp only [a, b] at result
  convert result using 1
  simp only [Iso.trans_assoc, exchangeConstantIso, constantRingIso,
      proEtaleConstantComparison, exchangeConstantRing, adicLisseConstantRing, coefficients]

private theorem cbcEvaluationLiftSquare
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    [Abelian C] [Abelian A] [Abelian A'] [Abelian D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e e' : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (he : e = e') :
    (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ C A).obj F₁)
      (F₂ := (Functor.whiskeringRight ℕᵒᵖ A D).obj F₂)
      (G₁ := (Functor.whiskeringRight ℕᵒᵖ C A').obj G₁)
      (G₂ := (Functor.whiskeringRight ℕᵒᵖ A' D).obj G₂)
      (termwiseSquareIso e)).hom =
      (Functor.mapDerivedCategorySquareIso
        (towerSquare F₁ F₂ G₁ G₂ e')).hom := by
  rw [towerSquare_eq, he]
  rfl

private theorem cbcEvaluationConstantTowerSquare {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (sq : ChosenCartesianSquare k r p i) :
    (exchangeConstantSquare (A := B) sq).exchangeTowerSquare =
      squareG B k r p i sq.w := by
  apply (towerSquare_localization (exchangeConstantSquare (A := B) sq)).symm.trans
  apply Iso.ext
  exact (cbcEvaluationLiftSquare (modulePullback B i) (modulePullback B r)
    (modulePullback B p) (modulePullback B k) _ _
    (cbcEvaluationConstantModuleSquare B k r p i sq)).trans
      (squareG_lift B k r p i sq.w).symm

private theorem cbcEvaluationConstantTowerMate {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (sq : ChosenCartesianSquare k r p i) :
    (exchangeConstantSquare (A := B) sq).exchangeTowerMate =
      exchange B k r p i sq.w := by
  unfold StrictTowerRingedSquare.exchangeTowerMate exchange
  rw [cbcEvaluationConstantTowerSquare B k r p i sq]
  rfl

private theorem cbcEvaluationMappedCombine
    {D E D' E' : Type*}
    [Category D] [Category E] [Category D'] [Category E']
    (F : D ⥤ E) (T : D ⥤ D') (U : E ⥤ E') (F' : D' ⥤ E')
    (δ : ∀ Q : D, U.obj (F.obj Q) ⟶ F'.obj (T.obj Q))
    {Q Q' : D} {V V' Z Z' : D'}
    (β : Q ⟶ Q') (j : T.obj Q' ⟶ V) (x : V ⟶ V')
    (z : T.obj Q ⟶ Z) (m : Z ⟶ Z') (β' : Z' ⟶ V')
    {L : E} {A B C : E'} (e : L ⟶ F.obj Q)
    (a : U.obj L ⟶ A) (b : A ⟶ B) (h : B ⟶ C)
    (c : B ⟶ F'.obj Z) (c' : C ⟶ F'.obj Z')
    (hnat : U.map (F.map β) ≫ δ Q' = δ Q ≫ F'.map (T.map β))
    (he : U.map e ≫ δ Q ≫ F'.map z = a ≫ b ≫ c)
    (hb : T.map β ≫ j ≫ x = z ≫ m ≫ β')
    (hn : c ≫ F'.map m = h ≫ c') :
    U.map (e ≫ F.map β) ≫ (δ Q' ≫ F'.map j ≫ F'.map x) =
      (a ≫ b ≫ h) ≫ (c' ≫ F'.map β') := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  rw [← F'.map_comp, ← F'.map_comp, hb, F'.map_comp, F'.map_comp]
  rw [reassoc_of% he, reassoc_of% hn]

/-- Evaluation describes the actual strict composite using the normalized finite mates.
It does not reconstruct a tower map from evaluations.
Source: blueprint strict realization, proof step 10; Stacks 07A7 and 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: evaluation commutes with exact G and J and evaluates their units termwise.
Its direct-image comparison is the mate of the pullback/evaluation comparison.
The mate correspondence therefore identifies evaluation of the proper factor
with cbcRealizationSingleProper. Transpose the open inverse: both sides are the
same evaluated open unit, hence agree. Compose these two equalities, using
naturality of evalR at beta. On quotient objects, constant/completed finite
reduction and strictTowerExchangeMateNormalization identify the proper mate with
the specified finite etale exchange; finite open scalar compatibility does the
same for the open mate, retaining the P_n actions and their quotient transitions. -/
theorem completeProetaleStrictTowerRealization_evaluation
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :
    (ProEtale.StrictTower.ev A Y' n).map
        (cbcRealizationStrict (A := A) c c' gbar sp sj M) ≫
        cbcRealizationEvalTarget (A := A) c' g' M n =
      cbcRealizationEvalSource (A := A) c g M n ≫
        cbcRealizationFinite (A := A) c c' gbar sp sj ((ProEtale.StrictTower.ev A X n).obj M) := by
  let sjp := IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd
  have he := evaluation_exchange A gbar c'.g c.g g sp.w ((J A c.i).obj M) n
  have hb := openBetaEvaluation A g' c'.i c.i gbar sj.w sjp M n
  have he' := (congrArg
    (fun e : R A c.g ⋙ G A g ⟶ G A gbar ⋙ R A c'.g ↦
      (ev A Y' n).map (e.app ((J A c.i).obj M)) ≫
        (evalR A c'.g n).app ((G A gbar).obj ((J A c.i).obj M)) ≫
        (ordinaryR A c'.g).map ((evalG A gbar n).hom.app ((J A c.i).obj M)))
    (cbcEvaluationConstantTowerMate A gbar c'.g c.g g sp)).trans he
  have result := cbcEvaluationMappedCombine
    (Q := (G A gbar).obj ((J A c.i).obj M))
    (Q' := (J A c'.i).obj ((G A g').obj M))
    (R A c'.g) (ev A c'.Z n) (ev A Y' n)
    (ordinaryR A c'.g) (fun Q ↦ (evalR A c'.g n).app Q)
    ((beta A g' c'.i c.i gbar sj.w sjp).hom.app M)
    ((evalJ A c'.i n).hom.app ((G A g').obj M))
    ((ordinaryJ A c'.i).map ((evalG A g' n).hom.app M))
    ((evalG A gbar n).hom.app ((J A c.i).obj M))
    ((ordinaryG A gbar).map ((evalJ A c.i n).hom.app M))
    ((openBetaSingle A g' c'.i c.i gbar sj.w sjp).hom.app ((ev A X n).obj M))
    ((exchangeConstantSquare (A := A) sp).exchangeTowerMate.app ((J A c.i).obj M))
    ((evalG A g n).hom.app ((R A c.g).obj ((J A c.i).obj M)))
    ((ordinaryG A g).map ((evalR A c.g n).app ((J A c.i).obj M)))
    ((ordinaryG A g).map ((ordinaryR A c.g).map ((evalJ A c.i n).hom.app M)))
    ((ordinaryE A gbar c'.g c.g g sp.w).app ((ev A c.Z n).obj ((J A c.i).obj M)))
    ((ordinaryE A gbar c'.g c.g g sp.w).app ((ordinaryJ A c.i).obj ((ev A X n).obj M)))
    ((evalR A c'.g n).naturality
      ((beta A g' c'.i c.i gbar sj.w sjp).hom.app M))
    he' hb ((ordinaryE A gbar c'.g c.g g sp.w).naturality
      ((evalJ A c.i n).hom.app M)).symm
  exact result

end Evaluation

attribute [local irreducible] cbcRealizationResLimit cbcRealizationPushLimit
  cbcRealizationOpenLimit cbcRealizationDerivedScalarOpen cbcRealizationSource
  cbcRealizationTarget

private def cbcReductionOpenNatIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    completedReductionTower U d ⋙ cbcRealizationJ d j ≅
      cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d :=
  NatIso.ofComponents (fun K ↦ (cbcRealizationReduction d j K).symm)
    (fun k ↦ (cbcRealizationReductionInv_properties d j).2 _ _ k)

private def cbcQuotientOpenNatIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
        exchangeTowerRes d T ≅
      completedReductionTower U d ⋙ exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j :=
  Functor.isoWhiskerRight (cbcReductionOpenNatIso d j).symm (exchangeTowerRes d T) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d) (cbcRealizationTowerScalarOpen d j)

private def cbcPullLimitNatIso {U T : Scheme.{t}} (u : U ⟶ T) :
    d.completedPull u ⋙ (cbcRealizationRes d U).mapDerivedCategory ≅
      completedReductionTower T d ⋙ exchangeTowerRes d T ⋙
        ProEtale.StrictTower.G A u ⋙ completedRlim U (exchangeConstantRing U A) :=
  Functor.isoWhiskerLeft (completedReductionTower T d ⋙ d.towerPull u)
      (cbcRealizationResLimit d U) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower T d)
      (Functor.isoWhiskerRight (exchangeResPull d u)
        (completedRlim U (exchangeConstantRing U A)))

private def cbcSourceNatIso (c : Compactification f) (g : Y' ⟶ Y) :
    cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g ⋙
        (cbcRealizationRes d Y').mapDerivedCategory ≅
      completedReductionTower X d ⋙ exchangeTowerRes d X ⋙ ProEtale.StrictTower.J A c.i ⋙
        ProEtale.StrictTower.R A c.g ⋙ ProEtale.StrictTower.G A g ⋙
          completedRlim Y' (exchangeConstantRing Y' A) := by
  let pi : d.push c.g ⋙ completedReductionTower Y d ≅
      completedReductionTower c.Z d ⋙ d.towerPush c.g :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection c.g K))
      (fun k ↦ (d.towerProjection_properties c.g _).2.1 _ k)
  exact Functor.isoWhiskerLeft (cbcDerivedOpenShriek d c.i c.isOpenImmersion)
      (Functor.isoWhiskerRight pi
        (d.towerPull g ⋙ completedRlim Y' (d.completedRing Y') ⋙
          (cbcRealizationRes d Y').mapDerivedCategory)) ≪≫
    Functor.isoWhiskerLeft
      (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ completedReductionTower c.Z d ⋙
        d.towerPush c.g ⋙ d.towerPull g) (cbcRealizationResLimit d Y') ≪≫
    Functor.isoWhiskerLeft
      (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ completedReductionTower c.Z d)
      (Functor.isoWhiskerRight (exchangeCornerB d c.g g)
        (completedRlim Y' (exchangeConstantRing Y' A))) ≪≫
    Functor.isoWhiskerRight (cbcQuotientOpenNatIso d c.i)
      (ProEtale.StrictTower.R A c.g ⋙ ProEtale.StrictTower.G A g ⋙
        completedRlim Y' (exchangeConstantRing Y' A))

private def cbcTargetNatIso (c' : Compactification f') (g' : X' ⟶ X)
    [QuasiCompact c'.i] :
    completedReductionTower X d ⋙ exchangeTowerRes d X ⋙ ProEtale.StrictTower.G A g' ⋙
        ProEtale.StrictTower.J A c'.i ⋙ ProEtale.StrictTower.R A c'.g ⋙
          completedRlim Y' (exchangeConstantRing Y' A) ≅
      d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g ⋙
        (cbcRealizationRes d Y').mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (completedReductionTower X d ⋙ exchangeTowerRes d X ⋙ ProEtale.StrictTower.G A g' ⋙
        ProEtale.StrictTower.J A c'.i) (cbcRealizationPushLimit (A := A) c'.g).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (completedReductionTower X d ⋙ exchangeTowerRes d X ⋙ ProEtale.StrictTower.G A g')
        (cbcRealizationOpenLimit d c'.i).symm)
      (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor ≪≫
    Functor.isoWhiskerRight (cbcPullLimitNatIso d g').symm
      ((ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor) ≪≫
    Functor.isoWhiskerLeft (d.completedPull g')
      (Functor.isoWhiskerRight (cbcRealizationDerivedScalarOpen d c'.i).symm
        (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor) ≪≫
    Functor.isoWhiskerLeft
      (d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion)
      (cbcRealizationResPush d c'.g).symm

private theorem cbcSourceNatIso_hom_app (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :
    (cbcSourceNatIso d c g).hom.app K =
      (cbcRealizationSource d c c' gbar (g := g) K).hom := by
  simp only [cbcSourceNatIso, cbcRealizationSource, cbcQuotientOpenNatIso,
    cbcReductionOpenNatIso, cbcRealizationReduction, cbcRealizationQuotientOpen,
    AdicCoefficientDatum.towerH, Functor.comp_map, Functor.comp_obj,
    AdicCoefficientDatum.fourTowerCorners, Matrix.cons_val_one, Matrix.cons_val_zero,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp]

private theorem cbcTargetNatIso_hom_app (c' : Compactification f') (g' : X' ⟶ X)
    [QuasiCompact c'.i] (K : d.derived X) :
    (cbcTargetNatIso d c' g').hom.app K = (cbcRealizationTarget d c' g' K).hom := by
  simp only [cbcTargetNatIso, cbcRealizationTarget, cbcPullLimitNatIso,
    cbcRealizationPullLimit, Functor.comp_map, Functor.comp_obj,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]

/-- The strict realization and both canonical endpoint identifications are natural in K.
Source: blueprint strict realization, final paragraph
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: the quotient tensor comparison is a transpose of the natural open unit.
All scalar, projection and limit comparisons are natural transformations, and
proper/open factors are normalized adjunction mates. Compose their naturality
squares in the order of the definitions. No condition on the chosen lower bounds
of the finite origins is used, and maps of derived objects need no lift to a
chosen strict complex. -/
theorem completeProetaleStrictTowerRealization_naturality [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (K L : d.derived X) (k : K ⟶ L) :
    (cbcRealizationRes d Y').mapDerivedCategory.map
        ((d.completedPull g).map ((d.push c.g).map
          ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k))) ≫
        (cbcRealizationSource d c c' gbar (g := g) L).hom =
      (cbcRealizationSource d c c' gbar (g := g) K).hom ≫
        (completedRlim Y' (exchangeConstantRing Y' A)).map
          ((ProEtale.StrictTower.G A g).map ((ProEtale.StrictTower.R A c.g).map
            ((ProEtale.StrictTower.J A c.i).map
              ((exchangeTowerRes d X).map ((completedReductionTower X d).map k))))) ∧
    (completedRlim Y' (exchangeConstantRing Y' A)).map
        ((ProEtale.StrictTower.R A c'.g).map ((ProEtale.StrictTower.J A c'.i).map
          ((ProEtale.StrictTower.G A g').map
            ((exchangeTowerRes d X).map ((completedReductionTower X d).map k))))) ≫
        (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) L).hom =
      (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K).hom ≫
        (cbcRealizationRes d Y').mapDerivedCategory.map
          ((d.push c'.g).map ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
            ((d.completedPull g').map k))) := by
  constructor
  · simpa only [Functor.comp_map, Functor.comp_obj,
      cbcSourceNatIso_hom_app d c c' gbar] using (cbcSourceNatIso d c g).hom.naturality k
  · let : QuasiCompact c'.i := cbcRealizationOpenQC c c' gbar sj
    simpa only [Functor.comp_map, Functor.comp_obj, cbcTargetNatIso_hom_app]
      using (cbcTargetNatIso d c' g').hom.naturality k

/-- Source presentation for the ordered open factor, using the same quotient/open map.
Source: blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenSource (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :=
  cbcRealizationPullLimit d gbar ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K) ≪≫
    (completedRlim c'.Z (exchangeConstantRing c'.Z A)).mapIso
      ((ProEtale.StrictTower.G A gbar).mapIso (cbcRealizationQuotientOpen d c.i K))

/-- The target of the open factor uses inverse extension/limit, followed by the
inverse pullback presentation and scalar/open transport, in precisely this order.
Source: Stacks 09BP and blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenTarget (c' : Compactification f') (g' : X' ⟶ X)
    [qc : QuasiCompact c'.i] (K : d.derived X) :=
  ((cbcRealizationOpenLimit d c'.i).app
      ((ProEtale.StrictTower.G A g').obj
        ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K)))).symm ≪≫
    (ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.mapIso
      (cbcRealizationPullLimit d g' K).symm ≪≫
    ((cbcRealizationDerivedScalarOpen d c'.i).app ((d.completedPull g').obj K)).symm

/-- The published completed open factor, with its derived quasi-compactness instance.
Source: blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationOpenFactor [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  (cbcDatumCompletedExchange d sj r a ha).app K

end AlgebraicGeometry.Scheme
