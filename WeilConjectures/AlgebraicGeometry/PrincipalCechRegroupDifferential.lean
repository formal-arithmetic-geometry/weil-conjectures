/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechTotalRegrouping
import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # Differential compatibility of the explicit regrouping

Source: Stacks, Tag 08D1, signs of alternating total cochains
(blueprint: lem-sc-principal-cech-regroup-differential).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

end
end AlgebraicGeometry
