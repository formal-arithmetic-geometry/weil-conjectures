/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Nat.Choose.Basic
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.ScalarConeStalkVanishing
import WeilConjectures.AlgebraicGeometry.RestrictedScalarConeSplit
import WeilConjectures.AlgebraicGeometry.BinomialShiftBiproduct

/-! # Affine support from successive cones

Source: Stacks Project, Tag 08EK (Lemma 36.13.10), proof, cone construction
(blueprint: lem-sc-affine-support-iterated-cones).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
