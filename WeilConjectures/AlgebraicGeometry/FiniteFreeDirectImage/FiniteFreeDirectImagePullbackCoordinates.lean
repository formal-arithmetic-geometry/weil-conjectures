/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingComputed
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeOrdinaryPullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedFiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite-free coordinates for the computed scalar pullback comparison

Source: Stacks Project, Tags 03EL, 06YY and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

section DerivedBridge

universe w uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
  (T : A ⥤ B) [T.Additive] (E : DerivedCategory A ⥤ DerivedCategory B)
  (ε : DerivedCategory.Qh ⋙ E ⟶ T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ C) (G : B ⥤ D) (T' : C ⥤ D) [F.Additive] [G.Additive] [T'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (E' : DerivedCategory C ⥤ DerivedCategory D)
  (ε' : DerivedCategory.Qh ⋙ E' ⟶ T'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [IsIso ε] [IsIso ε']
  (χ : T ⋙ G ≅ F ⋙ T')

end DerivedBridge

section CoordinateColumns

universe uA1 vA1 uB1 vB1
open CategoryTheory CategoryTheory.Limits
variable {A : Type uA1} [Category.{vA1} A] [Preadditive A] [HasFiniteBiproducts A]
  {B : Type uB1} [Category.{vB1} B] [Preadditive B] [HasFiniteBiproducts B]
  (d : ℕ)

end CoordinateColumns

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
