/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Scalar coherence for derived systems

Source: Zheng, Construction 4.1 and Proposition 4.17; Stacks Tags 06YY,
07A4, 07A6 and 08J9 (blueprint: lem-coef-semilinear-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096

attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

section ExactTriangles

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

variable {A₀ A₁ A₂ A₃ : Type*}
  [Category A₀] [Category A₁] [Category A₂] [Category A₃]
  [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian A₃]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁]
  [HasDerivedCategory A₂] [HasDerivedCategory A₃]

variable (F : A₀ ⥤ A₁) (G : A₀ ⥤ A₂) (H : A₀ ⥤ A₃)
  (R : A₂ ⥤ A₁) (S : A₃ ⥤ A₂) (T : A₃ ⥤ A₁)
  [F.Additive] [G.Additive] [H.Additive] [R.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

end ExactTriangles

end WeilConjectures.SemilinearSections
