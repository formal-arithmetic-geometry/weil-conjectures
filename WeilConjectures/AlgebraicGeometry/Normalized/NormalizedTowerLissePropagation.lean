/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteNativeRelativeLisse
import WeilConjectures.AlgebraicGeometry.Relative.RelativeNilpotentLissity
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Propagation of lissity along a normalized adic tower

This is the nilpotent propagation step used by the common-strata theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace LissePropagationProof

attribute [local irreducible] restrictCancelIso

end LissePropagationProof

end AlgebraicGeometry.Scheme
