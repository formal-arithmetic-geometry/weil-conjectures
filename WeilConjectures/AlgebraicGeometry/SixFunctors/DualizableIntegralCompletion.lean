/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import WeilConjectures.AlgebraicGeometry.AdicCompletion.TensorIntegralReductionTower
import WeilConjectures.SixFunctors.ProEtale.InternalRoosOutputComplete
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Dualizable tensoring preserves integral derived completeness

The statement concerns the actual augmented completion used by the coefficient library.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

end AlgebraicGeometry.ProEtale
