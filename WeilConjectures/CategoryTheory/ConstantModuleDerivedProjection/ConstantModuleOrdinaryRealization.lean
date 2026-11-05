/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleDerivedComparisonData
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Ordinary constant-module realization of a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV (6), Modules on Sites, Tag 03EL,
and Cohomology on Sites, Tag 07A4
(blueprint: lem-sfb-constant-module-ordinary-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option linter.privateModule false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]

-- Cache the standard sheafification properties before the repeated section calculations.

attribute [local irreducible] presheafToSheaf

-- Keep chosen sheafification functors behind their naturality APIs.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarValue ring

-- The scalar action can be tested on the binary operation (x,y) ↦ b • x + y.
set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] CategoryTheory.sfbSheafTensorStructure
set_option backward.isDefEq.respectTransparency true

-- Transport through a monoidal equivalence, retaining an explicit tensor formula.
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] CategoryTheory.ConstantScalarRestriction.fixedMonoidal
  CategoryTheory.ConstantScalarRestriction.restrictionBraided

end CategoryTheory.ConstantModuleDerivedProjection
