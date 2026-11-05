/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryTriangleRows
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.Algebra.Homology.ScalarCoefficientTriangleBoundary

/-! # Universal base-change counits on distinguished triangles

Source: Stacks Project, Tag 06Y6, exactness and independence of derived change of rings.
(blueprint: lem-pc-base-derived-tensor-cohomology-triangle-rows). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

end ModuleCat
