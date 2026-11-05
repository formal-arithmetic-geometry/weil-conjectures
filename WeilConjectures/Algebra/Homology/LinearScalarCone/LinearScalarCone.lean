/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower

/-! # Localization of the explicit linear scalar cone

Source: Stacks, Tags 014A and 06YS, principal two-term complex.
(blueprint: def-coef-linear-scalar-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u w r
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.LinearScalarCone

variable {R : Type r} [Ring R] {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  [HasDerivedCategory.{w} A] (s : R)

end CochainComplex.LinearScalarCone
