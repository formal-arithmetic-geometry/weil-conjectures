/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.MarkedIdealOrder

/-! # Stalk order along a boundary hypersurface

Source: Bierstone--Milman, Functoriality in resolution of singularities, section 5,
formula (5.4), and Theorem 6.2, pp. 629--633
(blueprint: def-trf-marked-boundary-order).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.HilbertSamuel

/-- Order of an ideal along a boundary ideal at a point. A boundary missing the point
has order zero, including for the zero ideal. At a point on the boundary take the
supremum of the exponents of its stalk ideal containing the given stalk ideal; in
particular the zero ideal has infinite order there.
Source: BM, formula (5.4) and Theorem 6.2, pp. 629--633
(blueprint: def-trf-marked-boundary-order). -/
def boundaryOrder {X : Scheme.{u}} (I D : X.IdealSheafData) (x : X) : ℕ∞ := by
  classical
  exact if x ∈ D.support then
    ⨆ (v : ℕ) (_ : stalkIdeal I x ≤ stalkIdeal D x ^ v), (v : ℕ∞)
  else 0

end AlgebraicGeometry.HilbertSamuel
