/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Unbounded sections and localization of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6F and its K-injective proof
(blueprint: lem-sfb-unbounded-sections-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedSectionsLocalization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The common-universe module category is Grothendieck abelian by the proved
small-site ring-sheaf theorem. Source: Stacks, Section 07A5
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian R

/-- Evaluation at an object, followed by forgetting scalars.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev evaluation (W : C) : ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op W) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op W))) AddCommGrpCat.{u}

/-- Restriction is additive sectionwise.
Source: Stacks, Tags 03DJ and 08FI
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive := by
  constructor
  intro M N f g
  ext V x
  rfl

/-- Termwise restriction of an unbounded complex.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev restrictComplex (W : C) :=
  (SheafOfModules.overFunctor.{u} R W).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{u}]

/-- Unbounded derived evaluation, with scalars forgotten after evaluation.
Source: Stacks, Section 07A5 and Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedEvaluation (W : C) :
    DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (evaluation R W).rightDerivedFunctor

/-- Unbounded derived restriction. Since sectionwise restriction is exact, its total
right derived functor is the usual termwise restriction on the derived category.
Source: Stacks, Tags 03DJ, 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedRestriction (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    DerivedCategory (ringedSiteModules.{u} R) ⥤
      DerivedCategory (ringedSiteModules.{u} (R.over W)) :=
  (SheafOfModules.overFunctor.{u} R W).rightDerivedFunctor

end CategoryTheory.UnboundedSectionsLocalization
