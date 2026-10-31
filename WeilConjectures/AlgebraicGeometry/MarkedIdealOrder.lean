/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Length

/-! # Order of a quasi-coherent ideal at a scheme point

Source: BMT, arXiv:0905.3580, section 5.1
(blueprint: def-trf-marked-ideal-order).
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.HilbertSamuel

/-- Stalk ideal obtained from affine germs, using the existing quasi-coherent ideal data.
Source: BMT 5.1, order in the local ring
(blueprint: def-trf-marked-ideal-order). -/
noncomputable def stalkIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  ⨆ (U : X.affineOpens) (hx : x ∈ U.1),
    (I.ideal U).map (X.presheaf.germ U.1 x hx).hom

/-- Order, with infinity for the zero stalk ideal. Source: BMT 5.1
(blueprint: def-trf-marked-ideal-order). -/
noncomputable def order {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) : ℕ∞ :=
  ⨆ (q : ℕ) (_ : stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ q),
    (q : ℕ∞)

end AlgebraicGeometry.HilbertSamuel
