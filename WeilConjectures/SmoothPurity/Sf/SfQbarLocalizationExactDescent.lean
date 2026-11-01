/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationFiniteData
import WeilConjectures.CategoryTheory.StageSystem.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationShiftDescent

/-! # Exact descent on the general rational coefficient stages

Source: the algebraically closed-stage localization argument, coefficient
comparison and adjunction compatibility steps.
(blueprint: lem-sf-qbar-localization-exact-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
