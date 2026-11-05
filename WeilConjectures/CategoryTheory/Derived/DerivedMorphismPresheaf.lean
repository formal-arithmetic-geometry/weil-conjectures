/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Derived morphism presheaves on localized sites

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
section ExactFunctors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end ExactFunctors

section ExactAssociativity

variable {C₀ C₁ C₂ C₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  (H : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃)
  (GH : C₀ ⥤ C₂) (FG : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
  [H.Additive] [G.Additive] [F.Additive] [GH.Additive] [FG.Additive] [FGH.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

end ExactAssociativity

section ExactIdentity

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) (J : D ⥤ D)
  [F.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

end ExactIdentity

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
variable (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]

attribute [instance] derivedSliceMap_preservesFiniteColimits

variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

variable {J B} {A D}

variable (J B)

namespace DerivedLocalFunctor
variable {J B} {B' : Type (u + 1)} [CommRing B'] (T : DerivedLocalFunctor J B B')
variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

end DerivedLocalFunctor

variable {B' : Type (u + 1)} [CommRing B']

end CategoryTheory
