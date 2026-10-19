/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.IntegralReductionTowerUnrestricted
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact

/-!
# Ordinary and completed integral pullback

Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15;
Stacks Project, Tags 06YY and 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).

The ordinary pullback uses the adjoint of the completed coefficient map fixed by
all finite projections. The comparison is fixed on flat-term K-flat representatives
by the quotient augmentation and the zero second coordinate of the strict Roos cone.

## Main definitions

* `ordinaryIntegralDerivedPull`: ordinary unbounded ringed pullback before completion.
* `ordinaryIntegralCompletionChain`: the prescribed (quotients, zero) cone map.
* `ordinaryIntegralCompletionComparison`: its uniquely normalized derived descent.

## Main statements

* `ordinaryCompletedIntegralPullback`: constructibility and invertibility of this comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private def ordinaryRestrictionPushforwardIso
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {T S : Sheaf J RingCat.{u + 1}} {R R' : Sheaf K RingCat.{u + 1}}
    (α : T ⟶ S) (β : R ⟶ R')
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R')
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat J K).map β = α ≫ ψ) :
    SheafOfModules.pushforward.{u + 1} ψ ⋙ SheafOfModules.restrictScalars α ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.pushforward.{u + 1} φ := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · exact ((ModuleCat.restrictScalarsComp
        (α.hom.app U).hom (ψ.hom.app U).hom).app (M.val.obj (F.op.obj U))).symm ≪≫
      (ModuleCat.restrictScalarsCongr
        (congrArg (fun k ↦ (k.hom.app U).hom) h.symm)).app _ ≪≫
      (ModuleCat.restrictScalarsComp
        (φ.hom.app U).hom (β.hom.app (F.op.obj U)).hom).app _
  · intro U V i
    ext x
    rfl
  · intro M N a
    apply SheafOfModules.hom_ext
    ext U x
    rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The finite constant coefficient map adjoint to the constant-section inverse-image map.
Source: Stacks 0H7J (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralFiniteDirectRingMap (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      (proEtaleSheafDirectImage f RingCat.{u + 1}).obj (integralCoefficientSheaf l E X n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private theorem ordinaryConstantUnit
    (A : CommRingCat.{u + 1}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{u, u} f A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem ordinaryConstantMap_naturality
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
      coefficientProEtaleDirectRingMap.{u, u} f B =
    coefficientProEtaleDirectRingMap.{u, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B)) |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  have hY := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at hY
  erw [← Category.assoc, ← hY, Category.assoc, ordinaryConstantUnit,
    ← Category.assoc, ordinaryConstantUnit]
  exact congrArg (fun α ↦ α.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

/-- The adjoint completed ring map is uniquely determined by all its quotient projections.
Its inverse-image adjoint is exactly c_f of the statement.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the constant-section maps commute with quotient transitions, by their
sheafification universal property. Right adjoint direct image preserves limits.
The limit universal property supplies the displayed map and proves uniqueness. -/
theorem ordinaryIntegralDirectRingMap_existsUnique :
    ∃! ρ : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (completedIntegralCoefficientSheafUnrestricted l E X),
      ∀ n : ℕ, ρ ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
          ordinaryIntegralFiniteDirectRingMap l E f n := by
  let D := proEtaleSheafDirectImage f RingCat.{u + 1}
  let : D.IsRightAdjoint := (proEtaleSheafAdjunction f RingCat.{u + 1}).isRightAdjoint
  let a : integralCoefficientSheafSystem l E Y ⟶ integralCoefficientSheafSystem l E X ⋙ D :=
    NatTrans.ofOpSequence (ordinaryIntegralFiniteDirectRingMap l E f) (fun n ↦ by
      simp only [integralCoefficientSheafSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      change integralCoefficientSheafTransition l E Y n ≫
          ordinaryIntegralFiniteDirectRingMap l E f n =
        ordinaryIntegralFiniteDirectRingMap l E f (n + 1) ≫
          D.map (integralCoefficientSheafTransition l E X n)
      exact (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).congr_map
        (ordinaryConstantMap_naturality f
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)))
  let c : Cone (integralCoefficientSheafSystem l E X ⋙ D) :=
    ⟨_, (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ a⟩
  let h := isLimitOfPreserves D (limit.isLimit (integralCoefficientSheafSystem l E X))
  refine ⟨h.lift c, ?_, ?_⟩
  · intro n
    exact h.fac c (op n)
  · intro b hb
    apply h.hom_ext
    intro n
    simpa using (hb n.unop).trans (h.fac c n).symm

/-- The canonical completed coefficient map, in its direct-image adjoint form.
Source: Bhatt--Scholze, Lemma 6.5.9
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDirectRingMap :=
  (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose

/-- The actual sectionwise module direct image with this completed coefficient action.
Source: Stacks 03D1 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePush : integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The specified pushforward has the sheafified module Kan-extension left adjoint.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: transport to the already recorded small site models, form the presheaf
module Kan extension along the displayed ring map and sheafify. Transport its
adjunction back. Its right adjoint is the specified sectionwise module pushforward.
The left adjoint is B_X tensor over f-inverse B_Y with f-inverse of the module. -/
@[instance] theorem ordinaryIntegralModulePush_isRightAdjoint :
    (ordinaryIntegralModulePush l E f).IsRightAdjoint := by
  have : IsGrothendieckAbelian.{u + 1} (integralTowerModules l E X) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  have : PreservesLimitsOfSize.{u + 1, u + 1} (ordinaryIntegralModulePush l E f) := by
    constructor
    intro J _
    have : Small.{u + 1} J := inferInstance
    constructor
    intro K
    constructor
    intro c hc
    refine ⟨?_⟩
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    change IsLimit ((ModuleCat.restrictScalars
      ((ordinaryIntegralDirectRingMap l E f).hom.app U).hom).mapCone
        ((SheafOfModules.evaluation _ ((proEtaleBaseChange f).op.obj U)).mapCone c))
    have : PreservesLimit K
        (SheafOfModules.evaluation _ ((proEtaleBaseChange f).op.obj U)) := inferInstance
    exact isLimitOfPreserves _ (isLimitOfPreserves _ hc)
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating
    (isCoseparator_coseparator (integralTowerModules l E X)) _

/-- Ordinary ringed module pullback, fixed by its sheafified Kan-extension adjunction.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePull :
    integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullback.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The adjunction supplying the canonical tensor generators of ordinary pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModuleAdjunction :
    ordinaryIntegralModulePull l E f ⊣ ordinaryIntegralModulePush l E f :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullbackPushforwardAdjunction (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- Additivity of ordinary module pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: sectionwise pushforward is additive. Its adjunction makes its left adjoint
additive by the preadditive adjunction criterion. -/
@[instance] theorem ordinaryIntegralModulePull_additive :
    (ordinaryIntegralModulePull l E f).Additive := by
  have : (ordinaryIntegralModulePush l E f).Additive := by
    constructor
    intro M N a b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  exact (ordinaryIntegralModuleAdjunction l E f).left_adjoint_additive

/-- The canonical total left derived functor exists on the unbounded category.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: use lem-pc-kflat-resolution with independent site and coefficient sizes.
Exact inverse image followed by extension of scalars preserves quasi-isomorphisms
between flat-term K-flat complexes, by ringed-topoi-derived-pullback. Localization
of this resolving class gives the total left derived functor and its counit. -/
@[instance] theorem ordinaryIntegralPull_hasLeftDerived :
    ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
  sorry

/-- Ordinary unbounded derived ringed pullback, before completion.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDerivedPull :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- The counit of the specified ordinary total derived pullback.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullCounit :
    DerivedCategory.Qh ⋙ ordinaryIntegralDerivedPull l E f ⟶
      (ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- Termwise ordinary pullback on cochain representatives.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplex :=
  (ordinaryIntegralModulePull l E f).mapHomologicalComplex (.up ℤ)

/-- The ordinary computation map on a cochain representative, retaining its universal counit.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplexCounit (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralDerivedPull l E f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ordinaryIntegralPullComplex l E f).obj P) :=
  (ordinaryIntegralDerivedPull l E f).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (ordinaryIntegralPullCounit l E f).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((ordinaryIntegralPullComplex l E f).obj P)

/-- The ordinary computation map is invertible on every flat-term K-flat representative.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the resolving-class derived-pullback theorem computes the total left derived
functor on precisely these complexes. Its counit is invertible there. The remaining
factors are the canonical cochain-to-homotopy localization isomorphisms. -/
theorem ordinaryIntegralPullComplexCounit_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsIso (ordinaryIntegralPullComplexCounit l E f P.obj) := by
  sorry


private def ordinaryFinitePush (n : ℕ) :=
  coefficientProEtaleModuleDirectImage.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))

private def ordinaryFiniteAdjunction (n : ℕ) :
    integralOperationsLevelPullback l E f n ⊣ ordinaryFinitePush l E f n :=
  coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))

private def ordinaryReductionPushIso (n : ℕ) :
    ordinaryFinitePush l E f n ⋙ scalarReductionRestriction l E Y n ≅
      scalarReductionRestriction l E X n ⋙ ordinaryIntegralModulePush l E f := by
  let πY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
  let πX := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  have h : ordinaryIntegralDirectRingMap l E f ≫
      (proEtaleSheafDirectImage f RingCat.{u + 1}).map πX =
    πY ≫ ordinaryIntegralFiniteDirectRingMap l E f n :=
    (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec n
  exact ordinaryRestrictionPushforwardIso πY πX
    (ordinaryIntegralDirectRingMap l E f) (ordinaryIntegralFiniteDirectRingMap l E f n) h

private def ordinaryReductionAdjunction (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

private theorem ordinaryReductionUnit_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryReductionAdjunction l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  exact (scalarReductionExtension_adjunction l E W n).choose_spec M U x

private abbrev ordinaryFiniteAugmentationTarget (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E f n ⋙
    scalarReductionRestriction l E X n

private def ordinaryFiniteAugmentationAdjunct (n : ℕ) :
    𝟭 (integralTowerModules l E Y) ⟶
      ordinaryFiniteAugmentationTarget l E f n ⋙ ordinaryIntegralModulePush l E f :=
  (ordinaryReductionAdjunction l E Y n).unit ≫
    Functor.whiskerLeft (unrestrictedIntegralReductionFunctor l E Y n)
      (Functor.whiskerRight (ordinaryFiniteAdjunction l E f n).unit
        (scalarReductionRestriction l E Y n)) ≫
    Functor.whiskerLeft (unrestrictedIntegralReductionFunctor l E Y n ⋙
      integralOperationsLevelPullback l E f n) (ordinaryReductionPushIso l E f n).hom

private def ordinaryFiniteAugmentation (n : ℕ) :
    ordinaryIntegralModulePull l E f ⟶ ordinaryFiniteAugmentationTarget l E f n where
  app M := ((ordinaryIntegralModuleAdjunction l E f).homEquiv M _).symm
    ((ordinaryFiniteAugmentationAdjunct l E f n).app M)
  naturality {M N} a := by
    apply ((ordinaryIntegralModuleAdjunction l E f).homEquiv M _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact (ordinaryFiniteAugmentationAdjunct l E f n).naturality a

private theorem ordinaryFiniteAugmentation_apply (n : ℕ)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((ordinaryFiniteAugmentation l E f n).app M).val.app
        (op ((proEtaleBaseChange f).obj V))
        (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) =
      integralOperationsPullbackGenerator l E f n
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
          (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x) := by
  have h := ((ordinaryIntegralModuleAdjunction l E f).homEquiv M _).apply_symm_apply
    ((ordinaryFiniteAugmentationAdjunct l E f n).app M)
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun k ↦ k.val.app (op V) x) h
  change ((ordinaryFiniteAugmentation l E f n).app M).val.app
      (op ((proEtaleBaseChange f).obj V))
      (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) =
    integralOperationsPullbackGenerator l E f n
      ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
        (((ordinaryReductionAdjunction l E Y n).unit.app M).val.app (op V) x) at h'
  rw [ordinaryReductionUnit_apply] at h'
  exact h'

private theorem ordinaryPullbackHom_ext
    {M : integralTowerModules l E Y} {N : integralTowerModules l E X}
    (a b : (ordinaryIntegralModulePull l E f).obj M ⟶ N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      (a.val.app (op ((proEtaleBaseChange f).obj V)))
        (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) =
      (b.val.app (op ((proEtaleBaseChange f).obj V)))
        (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x)) :
    a = b := by
  apply ((ordinaryIntegralModuleAdjunction l E f).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact h V.unop x

private instance ordinaryFiniteAugmentationTarget_additive (n : ℕ) :
    (ordinaryFiniteAugmentationTarget l E f n).Additive := by
  have := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  have := integralOperationsLevelPullback_additive.{u, u} l E f n
  dsimp only [ordinaryFiniteAugmentationTarget, scalarReductionRestriction]
  infer_instance

private def ordinaryFiniteAugmentationComplex (n : ℕ) :
    ordinaryIntegralPullComplex l E f ⟶ integralOperationsPullbackLevel l E f n := by
  letI := ordinaryFiniteAugmentationTarget_additive l E f n
  exact NatTrans.mapHomologicalComplex (ordinaryFiniteAugmentation l E f n) (.up ℤ)

private theorem ordinaryFiniteAugmentationComplex_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    (((ordinaryFiniteAugmentationComplex l E f n).app P).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
        (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  exact ordinaryFiniteAugmentation_apply l E f n (P.X i) V x

private theorem ordinaryFiniteAugmentationComplex_transition (n : ℕ) :
    ordinaryFiniteAugmentationComplex l E f (n + 1) ≫
        integralOperationsPullbackTransition l E f n =
      ordinaryFiniteAugmentationComplex l E f n := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.Hom.ext
  funext i
  apply ordinaryPullbackHom_ext l E f
  intro V x
  change (((integralOperationsPullbackTransition l E f n).app P).f i).val.app
      (op ((proEtaleBaseChange f).obj V))
      ((((ordinaryFiniteAugmentationComplex l E f (n + 1)).app P).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
          (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x)) = _
  rw [ordinaryFiniteAugmentationComplex_apply]
  rw [show integralOperationsPullbackTransition l E f n =
    (integralOperationsPullbackTransition_existsUnique l E f n).exists.choose from rfl]
  rw [(integralOperationsPullbackTransition_existsUnique l E f n).exists.choose_spec]
  rw [show unrestrictedIntegralTransition l E Y n =
    (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose from rfl]
  rw [(unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec]
  simp only [map_one]
  exact (ordinaryFiniteAugmentationComplex_apply l E f n P i V x).symm

private def ordinaryQuotientAugmentation :
    ordinaryIntegralPullComplex l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f where
  app P := NatTrans.ofOpSequence
    (fun n ↦ (ordinaryFiniteAugmentationComplex l E f n).app P) (fun n ↦ by
      simp only [Functor.comp_obj, Functor.const_obj_map,
        integralOperationsPullbackTowerFunctor, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (ordinaryFiniteAugmentationComplex l E f n).app P =
        (ordinaryFiniteAugmentationComplex l E f (n + 1)).app P ≫
          (integralOperationsPullbackTransition l E f n).app P
      exact (congrArg (fun a ↦ a.app P)
        (ordinaryFiniteAugmentationComplex_transition l E f n)).symm)
  naturality {P Q} a := by
    apply NatTrans.ext
    funext n
    exact (ordinaryFiniteAugmentationComplex l E f n.unop).naturality a

/-- The quotient maps, as one natural map of strict towers, are uniquely fixed on generators.
The formula is 1 tensor q ↦ 1 tensor (q tensor 1); completed linearity gives
b tensor q ↦ 1 tensor (q tensor pi_n(b)) on every inverse-image generator.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY, 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the completed coefficient map commutes with each quotient by its defining
projection equation. Thus the displayed map is balanced, linear and restriction
compatible. Sheafification gives the module maps; applying them degreewise gives
chain maps. Coefficient reduction preserves one, so consecutive transition squares
commute. The same generator equality proves naturality. Locally the scalar multiples
of restrictions of adjunction-unit generators generate pullback, giving uniqueness. -/
theorem ordinaryIntegralQuotientAugmentation_existsUnique :
    ∃! a : ordinaryIntegralPullComplex l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((a.app P).app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))
          (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  refine ⟨ordinaryQuotientAugmentation l E f, ?_, ?_⟩
  · intro P n i V x
    exact ordinaryFiniteAugmentationComplex_apply l E f n P i V x
  · intro a ha
    apply NatTrans.ext
    funext P
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.Hom.ext
    funext i
    apply ordinaryPullbackHom_ext l E f
    intro V x
    exact (ha P n.unop i V x).trans
      (ordinaryFiniteAugmentationComplex_apply l E f n.unop P i V x).symm

/-- The actual quotient augmentation, with all quotient transitions retained.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralQuotientAugmentation :=
  (ordinaryIntegralQuotientAugmentation_existsUnique l E f).exists.choose

/-- The product of the specified quotient maps.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralProductAugmentation
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      ∏ᶜ (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((ordinaryIntegralQuotientAugmentation l E f).app P).app (op n))

private theorem ordinaryCone_killed
    {A : Type*} [Category A] [Preadditive A]
    (C : ℕᵒᵖ ⥤ A) [HasProduct (fun n : ℕ ↦ C.obj (op n))]
    {B : A} (a : (Functor.const ℕᵒᵖ).obj B ⟶ C) :
    Pi.lift (fun n : ℕ ↦ a.app (op n)) ≫
      towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
        (fun n ↦ C.map (homOfLE (Nat.le_succ n)).op) = 0 := by
  apply Pi.hom_ext
  intro n
  have hn := a.naturality (homOfLE (Nat.le_succ n)).op
  simpa only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.assoc, Category.comp_id, Category.id_comp,
    Pi.lift_π, Pi.lift_π_assoc, zero_comp, Functor.const_obj_map] using
    sub_eq_zero.mpr (by simpa using hn)

/-- The strict quotient augmentation is killed by 1-s, with zero second cone cochain.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: after every product projection, the composite with 1-s is the difference
between consecutive quotient maps and is zero by the strict tower's naturality.
The differential of the zero cochain is zero. Product projections are jointly monic. -/
theorem ordinaryIntegralCompletionChain_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain ((ordinaryIntegralPullComplex l E f).obj P)
        (∏ᶜ fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (ordinaryIntegralProductAugmentation l E f P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
            (integralOperationsTowerStep
              ((integralOperationsPullbackTowerFunctor l E f).obj P))) = 0 := by
  have h : ordinaryIntegralProductAugmentation l E f P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)) =
      0 := by
    exact ordinaryCone_killed _ ((ordinaryIntegralQuotientAugmentation l E f).app P)
  rw [h]
  simp

/-- The prescribed chain map into Cone(1-s)[-1]: quotient maps and zero, respectively.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionChain
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E f).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)))
    (ordinaryIntegralProductAugmentation l E f P) 0
    (ordinaryIntegralCompletionChain_condition l E f P)

/-- The specified chain maps descend to a unique natural transformation.
Source: Stacks 06YY, 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the augmentation is natural on chain maps. Its strict cone map has a zero
second coordinate, so its naturality holds as chain maps, not just on projections.
Both representative constructions invert quasi-isomorphisms on the flat-term
K-flat class by ringed-topoi-derived-pullback and integral-operations-well-defined.
The resolving-class localization therefore descends the comparison. Its restriction
on that class is faithful, proving uniqueness and independence of the resolution. -/
theorem ordinaryIntegralCompletionComparison_existsUnique :
    ∃! η : ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        η.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          ordinaryIntegralPullComplexCounit l E f P.obj ≫
            DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) := by
  sorry

/-- The canonical completion comparison, uniquely fixed by the (quotients,0) chain map.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionComparison :
    ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f :=
  (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose

/-- Ordinary pullback of an integral constructible object is constructible, and its
specified completion map is invertible, naturally and independently of its resolution.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof:
1. Apply integral-stratified-perfect-characterization on Y. Obtain finitely many
constructible locally closed strata and pro-etale covers with bounded finite-projective
R-complexes as local models. The detailed-category comparison retains the same completed
ring, reduction functors and uniform reduction bound.
2. Base change the strata along f and discard empty strata. They are locally closed,
constructible, disjoint and cover X. Base-changed trivializing families remain covering
by topos-functoriality-inverse-image.
3. The completed coefficient maps agree under composition after all finite projections.
Ringed-derived-monoidal-comparisons, the ordinary immersion restriction assertion of
immersion-completed-pullback-comparison, and ringed-derived-slice-localization therefore
compute ordinary pullback locally as B_V tensor_R L. Finite projective summands and their
bounded complexes compute derived pullback, so these are the required perfect models.
4. Apply integral-stratified-perfect-characterization on X: the output is in the detailed
integral category, with one uniform bound for its reductions, and is intrinsically complete.
5. For a good resolution Q, ordinary pullback F is K-flat with flat terms by
ringed-topos-kflat-pullback. The finite constant inverse-image map and exact finite
pullback identify F tensor D_n with f_n-star(Q tensor C_n). On tensors the map sends
(b tensor q) tensor a to 1 tensor (q tensor pi_n(b)a); the inverse inserts one. The
formulas commute with the actual quotient transitions and carry quotient units to the
augmentation used above. Use proetale-constant-exact and left-exact-site-inverse-image-tensor.
6. The valuation ring is a Noetherian DVR with finite quotients, by extension-integers-dvr
and valued-dvr-finite-quotients. The two-term complexes [R --t^n--> R] resolve the quotients.
Koszul-reconstruction makes the completion unit of the complete output invertible.
Exact products and integral-operations-well-defined compute that unit by the strict Roos
cone. The tower identification in step 5 carries both coordinates to the specified
chain map, hence gives invertibility of this very comparison.
7. On any chain map of good resolutions, both quotient-augmentation composites send
b tensor q to 1 tensor (v(q) tensor pi_n(b)). Their products and zero second coordinates
therefore commute strictly. Localizing proves naturality and independence under all
canonical resolution comparisons. No separatedness or base-field structure is used. -/
theorem ordinaryCompletedIntegralPullback
    [IsNoetherian X] [IsNoetherian Y]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (_hXinv : IsUnit (l : Γ(X, ⊤))) (_hYinv : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((ordinaryIntegralDerivedPull l E f).obj K) ∧
      IsIso ((ordinaryIntegralCompletionComparison l E f).app K) := by
  sorry

end WeilConjectures
