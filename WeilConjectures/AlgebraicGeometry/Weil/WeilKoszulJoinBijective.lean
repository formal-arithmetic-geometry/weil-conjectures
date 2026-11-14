/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijectivePositive
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijectiveNonpositive

/-! # Bijectivity of graded exterior multiplication

Source: Stacks Project, More on Algebra, Tag 0664.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- Exterior multiplication is bijective in each degree, independently of any differential.

Source: Stacks Project, Tag 0664. -/
theorem koszulJoinGraded_bijective {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (i : ℤ) :
    Function.Bijective (koszulJoinGraded r a m i).hom := by
  by_cases hi : i ≤ 0
  · exact koszulJoinGraded_bijective_of_nonpositive r a m i hi
  · exact koszulJoinGraded_bijective_of_pos r a m i (by omega)

end AlgebraicGeometry.Scheme
