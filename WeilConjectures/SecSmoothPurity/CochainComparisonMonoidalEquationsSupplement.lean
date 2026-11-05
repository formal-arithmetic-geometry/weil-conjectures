/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Monoidal equations for the canonical cochain comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-cochain-comparison-monoidal-equations)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] HomologicalComplex.monoidalCategoryStruct

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

section Generic
variable {A : Type uE} [Category.{vE} A] [MonoidalCategory A]
  {B : Type uD} [Category.{vD} B] [MonoidalCategory B]

end Generic

-- The graded tensor coproduct choices are shared throughout this module.
attribute [local instance] gradedTensorLeftR gradedTensorLeftS gradedTensorRightR
  gradedTensorRightS

attribute [local irreducible] SheafOfModules.monoidalCategory

-- Work only with the normalized total comparison, before introducing lifted instances.
-- Assemble the ordinary structure and identify its total comparison.
end CategoryTheory.CochainPullback
