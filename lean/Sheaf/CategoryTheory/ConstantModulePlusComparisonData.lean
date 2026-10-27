/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Bounded-below constant-module comparison data

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6;
Derived Categories, Tags 013K and 070J
(blueprint: def-sfb-constant-module-plus-comparison-data).

The localization, Hom, tensor and inclusion equations retain all the canonical normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
-- Match the additive structures in the shared localization predicates.
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]

/-- Bounded-below comparisons, inclusion squares and counits agree with the unbounded data.
Source: Stacks Tags 013K, 070J and 07A6
(blueprint: def-sfb-constant-module-plus-comparison-data). -/
structure PlusIdentification (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (e : DerivedIdentification d x o t cJ cK) where
  left : d.pullR.mapDerivedCategoryPlus ⋙ (restriction K A).mapDerivedCategoryPlus ≅
    (restriction J A).mapDerivedCategoryPlus ⋙ d.pullA.mapDerivedCategoryPlus
  right : d.pushR.rightDerivedFunctorPlus ⋙ (restriction J A).mapDerivedCategoryPlus ≅
    (restriction K A).mapDerivedCategoryPlus ⋙ d.pushA.rightDerivedFunctorPlus
  left_inclusion : ∀ M : DerivedCategory.Plus (Modules J A),
    DerivedCategory.Plus.ι.map (left.hom.app M) = e.left.hom.app M.obj
  right_inclusion : ∀ N : DerivedCategory.Plus (Modules K A),
    DerivedCategory.Plus.ι.map (right.hom.app N) ≫
      d.pushA.rightDerivedFunctorPlusCompatibility.hom.app
        ((restriction K A).mapDerivedCategoryPlus.obj N) =
    (onDerived J A).map (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      e.right.hom.app N.obj
  hom : ∀ (M : DerivedCategory.Plus (Modules J A))
    (N : DerivedCategory.Plus (Modules K A))
    (f : d.pullR.mapDerivedCategoryPlus.obj M ⟶ N),
    d.fixedAdj.derivedPlus.homEquiv _ _
        (left.inv.app M ≫ (restriction K A).mapDerivedCategoryPlus.map f) =
      (restriction J A).mapDerivedCategoryPlus.map
        (d.ringAdj.derivedPlus.homEquiv M N f) ≫ right.hom.app N
  ring_counit : ∀ N : DerivedCategory.Plus (Modules K A),
    d.pullR.mapDerivedCategoryPlusCompatibility.hom.app
        (d.pushR.rightDerivedFunctorPlus.obj N) ≫
      d.pullR.mapDerivedCategory.map
        (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      d.ringAdj.mapDerivedCategoryRightDerivedAdjunction.counit.app N.obj =
        DerivedCategory.Plus.ι.map (d.ringAdj.derivedPlus.counit.app N)
  fixed_counit : ∀ N : DerivedCategory.Plus (Fixed K A),
    d.pullA.mapDerivedCategoryPlusCompatibility.hom.app
        (d.pushA.rightDerivedFunctorPlus.obj N) ≫
      d.pullA.mapDerivedCategory.map
        (d.pushA.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction.counit.app N.obj =
        DerivedCategory.Plus.ι.map (d.fixedAdj.derivedPlus.counit.app N)


end CategoryTheory.ConstantModuleDerivedProjection
