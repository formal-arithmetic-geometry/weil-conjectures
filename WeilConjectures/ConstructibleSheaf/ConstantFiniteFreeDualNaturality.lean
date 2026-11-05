/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import Mathlib.LinearAlgebra.Contraction
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Natural dual comparison for constant finite free sheaves -/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

open TensorProduct

-- The following contraction calculations follow the dual-basis proof in
-- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed.
-- We retain the explicit pairing, so no arbitrary dualizable witness is chosen.

end AlgebraicGeometry.Scheme
