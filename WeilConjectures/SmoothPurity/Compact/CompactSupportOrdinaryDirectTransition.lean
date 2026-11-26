/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectLeftSections
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectRightSections

/-! # Ordinary coefficient compatibility of direct evaluation

Ordinary native direct evaluation is compatible with the horizontal coefficient transition
maps.

## Implementation details

`moduleEvalP`, `compactSupportDirectModel` and the ordinary scalar direct-image comparison are
the identity on section carriers, so the statement is proved sectionwise.

## References

* Stacks Project, Tags 03DI, 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] coefficientSequenceEvaluation_additiveInstance
  HasDerivedCategory.standard
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Compare the named scalar sheaves without unfolding their sheafification constructions.
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf Functor.leftAdjoint
  HasDerivedCategory.standard MorphismProperty.Over.pullback

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

-- The identities compare concrete scalar actions on the same section carriers.
/-- Ordinary native direct evaluation commutes with the horizontal coefficient transitions
from level `m` to level `n`. -/
theorem compactSupportOrdinaryDirectTransition {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceModules.{u, u} l E Z) :
    (compactSupportOrdinaryCoefficientTransition l E Y h).app
        ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g).obj M) ≫
      (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h)).map
        ((compactSupportOrdinaryDirectEvaluation l E g n).hom.app M) ≫
      (proEtaleCoefficientDirectImageComparison g
        (compactSupportLevelQuotient l E m n h)).hom.app
          ((coefficientSequenceEvaluation.{u, u} l E Z n).obj M) =
    (compactSupportOrdinaryDirectEvaluation l E g m).hom.app M ≫
      (proEtaleConstantModuleDirectImage g
        (Padic.coefficientExtensionRing l E (m + 1))).map
          ((compactSupportOrdinaryCoefficientTransition l E Z h).app M) := by
  ext V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hl := compactSupportOrdinaryDirectLeftSections l E g h M V x
  have hr := compactSupportOrdinaryDirectRightSections l E g h M V x
  exact eq_of_heq (hl.trans hr.symm)

end WeilConjectures
