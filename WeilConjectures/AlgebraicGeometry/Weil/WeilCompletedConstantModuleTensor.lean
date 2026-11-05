/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Ordinary tensor comparison for completed constant modules

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
section Normalization

universe vC uC vD uD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

-- An automorphism of the tensor unit acts naturally on every object.

end Normalization

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
