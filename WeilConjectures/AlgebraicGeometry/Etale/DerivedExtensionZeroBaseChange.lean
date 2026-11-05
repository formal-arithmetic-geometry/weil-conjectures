/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.CategoryTheory.DerivedExactSquare
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Derived extension-by-zero base change

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
cor-cbc-derived-extension-zero-base-change; Stacks Tags 03S6, 0F70 and 015F
(blueprint: cor-cbc-derived-extension-zero-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

section DerivedTools

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

end DerivedTools

section Underived

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

end Underived

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Etale
