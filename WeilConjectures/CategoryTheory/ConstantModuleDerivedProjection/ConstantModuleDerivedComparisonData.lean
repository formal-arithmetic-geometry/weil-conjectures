/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Normalized derived constant-module comparison data

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6;
Derived Categories, Tags 013K and 070J
(blueprint: def-sfb-constant-module-derived-comparison-data).

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
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open CategoryTheory.Abelian
namespace CategoryTheory.ConstantModuleDerivedProjection
/-- The left localization equation with its ordinary functors kept abstract.
Source: Stacks Tags 07A4 and 07A6
(blueprint: def-sfb-constant-module-derived-comparison-data). -/
def LeftLocalizationCondition
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [Abelian B] [Abelian E] [Abelian F] [Abelian H]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasDerivedCategory F] [HasDerivedCategory H]
    (L : B ⥤ E) (L' : F ⥤ H) (S : B ⥤ F) (T : E ⥤ H)
    [L.Additive] [L'.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (oL : L ⋙ T ≅ S ⋙ L')
    (left : L.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ L'.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex B ℤ,
    left.hom.app (DerivedCategory.Q.obj P) ≫
      L'.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app P) ≫
      L'.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) =
    T.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      T.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oL (.up ℤ)).hom.app P)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]

/-- Localization normalization of the inverse-image comparison.
Source: Stacks Tags 07A4 and 07A6
(blueprint: def-sfb-constant-module-derived-comparison-data). -/
def LeftLocalizationSquare (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (left : d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory) : Prop :=
  LeftLocalizationCondition d.pullR d.pullA (restriction J A) (restriction K A)
    o.left left

end CategoryTheory.ConstantModuleDerivedProjection
