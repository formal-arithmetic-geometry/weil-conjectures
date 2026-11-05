/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernel

/-! # Dual of a finite constant module sheaf

Source: the finite presentation argument in the docstring of
`WeilConjectures/ConstructibleSheaf/Monoidal.lean`, `IsFiniteLocallyConstantSheaf.ihom_unit`.
(blueprint: lem-weil-pbc-constant-module-dual)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
