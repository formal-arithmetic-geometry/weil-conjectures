/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent

/-! # The coefficient quotient sequence tensored with a flat module

Source: Stacks Project, Cohomology on Sites, Tags 06YP and 06YY.
(blueprint: lem-cbc-regular-quotient-flat-sequence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.RegularQuotientCone
open SheafOfModules.IndependentExtensionTensor

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local instance] monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

end SheafOfModules.RegularQuotientCone
