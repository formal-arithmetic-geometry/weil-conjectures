/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle

/-! # Canonical Roos triangle of a completed-coefficient tower

Source: Stacks Tags 0941, 079P, 0BK6 and 0BK7.
(blueprint: lem-coef-constant-tower-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasLimitsOfShape ℕᵒᵖ A]

variable [HasCountableProducts A] [CountableAB4Star A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

end CategoryTheory

namespace WeilConjectures
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

end WeilConjectures
