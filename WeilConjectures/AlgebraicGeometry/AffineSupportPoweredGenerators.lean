/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectIntoSupportPowerTorsion
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh

/-! # Powered generators of a closed support

Source: Stacks Project, Tag 08EK, proof, first paragraph; Tag 08EJ.
(blueprint: lem-sc-affine-support-powered-generators).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[simp] private theorem globalFamily_top (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    (globalFamily X a).val (op ⊤) = a := by
  dsimp [globalFamily]
  simp

end AlgebraicGeometry.Scheme
