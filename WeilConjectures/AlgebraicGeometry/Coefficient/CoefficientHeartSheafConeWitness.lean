/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # The sheaf part of coefficient generation
Source: blueprint generation, Single sheaves paragraph.
(blueprint: lem-sfb-coefficient-heart-sheaf-cone-witness)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ₀] [IsCommMonObj Λ₀]

end AlgebraicGeometry.ProEtale
