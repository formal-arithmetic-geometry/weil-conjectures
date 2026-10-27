/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CoefficientEtaleDerivedStalk
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.Paper.FiniteComparisonModelRealization

/-! # Fixed scalar presentations for local coefficient models

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA, and
Cohomology on Sites, Tags 094G and 094I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (B : Type w) [CommRing B]

/-- Constant-scalar restriction is an equivalence. Source: Stacks 03CY.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
instance coefficientFixedScalarsEquivalence :
    (coefficientModelFixedScalars J B).IsEquivalence :=
  coefficientModelFixedScalars_isEquivalence J B

/-- Constant-scalar restriction is additive. Source: Stacks 03DA.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
instance coefficientModelFixedScalars_additive :
    (coefficientModelFixedScalars J B).Additive := by
  constructor
  intro M N f g
  ext U m
  rfl

/-- The standard localization of fixed-coefficient sheaves. Source: Stacks 05RU.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
abbrev CoefficientFixedDerivedCategory :=
  letI := HasDerivedCategory.standard (Sheaf J (ModuleCat.{w} B))
  DerivedCategory (Sheaf J (ModuleCat.{w} B))

/-- Exact change from intrinsic constant-ring modules to fixed scalars.
Source: Stacks 03DA and 05RU
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
def coefficientFixedDerivedScalars :
    ConstantCompletion.D (ConstantCompletion.constant J B) ⥤
      CoefficientFixedDerivedCategory J B :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J B))
  letI := HasDerivedCategory.standard (Sheaf J (ModuleCat.{w} B))
  (coefficientModelFixedScalars J B).mapDerivedCategory

/-- Slice restriction is additive. Source: Stacks 03DJ.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
instance coefficientFixedOver_additive (U : C) :
    (J.overPullback (ModuleCat.{w} B) U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Slice restriction is right exact. Source: Stacks 03DJ.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
instance coefficientFixedOver_colimits (U : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{w} B) U) :=
  ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
    (self := Adjunction.leftAdjoint_preservesColimits
      (Functor.sheafAdjunctionCocontinuous (Over.forget U) (ModuleCat.{w} B)
        (J.over U) J))⟩

/-- Exact slice restriction in standard fixed-scalar localizations. Source: Stacks 03DJ.
(blueprint: def-sfb-coefficient-fixed-derived-models). -/
def coefficientFixedDerivedRestriction (U : C) :
    CoefficientFixedDerivedCategory J B ⥤ CoefficientFixedDerivedCategory (J.over U) B :=
  letI := HasDerivedCategory.standard (Sheaf J (ModuleCat.{w} B))
  letI := HasDerivedCategory.standard (Sheaf (J.over U) (ModuleCat.{w} B))
  (J.overPullback (ModuleCat.{w} B) U).mapDerivedCategory

/-- A supplied constant cochain model on one fixed-scalar slice.
Source: Stacks 094G (blueprint: def-sfb-coefficient-fixed-derived-models). -/
def CoefficientFixedLocalModel
    (K : ConstantCompletion.D (ConstantCompletion.constant J B)) (U : C)
    (M : CochainComplex (ModuleCat.{w} B) ℤ) : Prop :=
  letI := HasDerivedCategory.standard (Sheaf (J.over U) (ModuleCat.{w} B))
  Nonempty ((coefficientFixedDerivedRestriction J B U).obj
      ((coefficientFixedDerivedScalars J B).obj K) ≅
    DerivedCategory.Q.obj
      (((constantSheaf (J.over U) (ModuleCat.{w} B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M))

end CategoryTheory
