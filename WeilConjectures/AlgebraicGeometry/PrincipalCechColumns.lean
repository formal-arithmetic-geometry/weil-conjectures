/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Explicit principal Čech columns and horizontal maps

Source: Stacks, Tag 08D1, alternating Čech double complex
(blueprint: def-sc-principal-cech-columns).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

end
end AlgebraicGeometry
