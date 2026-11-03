/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Actual semi-invariant section modules

Source: Milne, Algebraic Groups (2017), Section 18c and 22.48--22.49; Alper,
Section 9.7, immediately before Lemma 9.7.2, positive right-semi-invariance convention
(blueprint: def-sfb-rho-section-module-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry.RhoSection

/-- The actual coordinate algebra, with the scalar structure induced by the structure map.
Source: Milne, Section 18c (blueprint: def-sfb-rho-section-module-data). -/
abbrev Coordinate {F : Type u} [Field F] (G : Over (Spec (.of F))) :=
  ((algΓ (.of F)).obj G).unop

end AlgebraicGeometry.RhoSection
