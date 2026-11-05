/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.DerivedProjectionComparisonSquares
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarGeometricAdjunctions
public import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Constant modules, derived adjunctions and projection maps

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6;
Modules on Sites, Tag 03EL
(blueprint: def-sfb-constant-module-geometric-comparison-data).

The ordinary data below specify geometric inverse image and scalar extension on generalized
sections. Derived comparisons retain their localization squares, Hom bijections and counits.
The site object and morphism universes remain independent, including for small etale sites.
The ringed datum uses the landed independent-universe interface
`RingedToposMorphismOfUniverses` (blueprint: def-pur-ringed-topos-morphism-of-universes).
The two fixed-scalar OfUniverses helpers extend the imported constant-scalar interface
here; its landed declarations and DAG binding remain intact.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u v w a b c e ha hb hc he wa wb

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
open SheafOfModules.CanonicalTensorPullbackOfUniverses

namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory.ConstantModuleDerivedProjection

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type (max u v)) [CommRing A]

attribute [instance] GeometricData.leftExact GeometricData.pullR_additive
  GeometricData.pushR_additive

variable {J K A}

attribute [instance] ExactData.pullA_additive ExactData.pushA_additive
  ExactData.pullA_limits ExactData.pullA_colimits ExactData.pullR_limits ExactData.pullR_colimits
  ExactData.pullA_allColimits
  ExactData.pullR_allColimits

variable [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]

end CategoryTheory.ConstantModuleDerivedProjection
