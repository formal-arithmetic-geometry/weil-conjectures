/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Direct image on restricted coefficient towers

Source: Stacks Project, Tags 03D7 and 0941.
(blueprint: lem-sf-integral-ordinary-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  pullbackTensorSequenceRing completedIntegralCommRingProjectionUnrestricted
  sfCompletedCoefficientMap
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  coefficientSequenceEvaluation coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage proEtaleConstantDirectImageMap coefficientProEtaleDirectRingMap
  pullbackTensorSequenceBase pullbackTensorSequenceDirect SheafOfModules.restrictScalars

attribute [local irreducible] pullbackTensorSequenceDirectEvaluation

attribute [local irreducible] sfDirectImageRestrictionComparison

attribute [local irreducible] levelComparison

attribute [local irreducible] towerComparison

/-- The normalized finite comparisons form a unique isomorphism of coefficient towers.
Source: Stacks Project, Tags 03D1 and 0941; primitive realization Step 3.
(blueprint: lem-sf-integral-ordinary-tower-comparison).

Proof: compose restriction/evaluation, direct-image/evaluation, scalar restriction,
and the inverse restriction/evaluation comparison at each coefficient level.
Each factor is the identity on underlying sections. The specified horizontal maps
of restriction therefore make these isomorphisms natural in the tower index;
naturality in the input module is inherited from the four factors. This constructs
the isomorphism of towers. Equality on all component sections proves uniqueness. -/
theorem integralOrdinaryTowerComparison_legacy {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y ≅
      coefficientSequenceRestriction l E X ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCompletedModuleDirectImage l E f),
      ∀ (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEtᵒᵖ)
        (x : (((pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceRestriction l E Y).obj
          M).obj (op n)).val.obj V),
        HEq (((e.hom.app M).app (op n)).val.app V x) x := by
  refine ⟨towerComparison l E f, ?_, ?_⟩
  · intro M n V x
    rw [towerComparison_component]
    exact levelComparison_sections l E f n M V x
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext V x
    have h := levelComparison_sections l E f n.unop M V x
    rw [← towerComparison_component l E f M n.unop] at h
    exact eq_of_heq ((he M n.unop V x).trans h.symm)

end WeilConjectures.IntegralSystemRealization
