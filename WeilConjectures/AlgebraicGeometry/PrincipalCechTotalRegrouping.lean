/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Regrouping the graded terms of principal Čech columns

Source: Stacks, Tag 08D1, alternating total cochains
(blueprint: lem-sc-principal-cech-total-regrouping).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex (SheafOfModules.{u}
  (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

end
end AlgebraicGeometry
