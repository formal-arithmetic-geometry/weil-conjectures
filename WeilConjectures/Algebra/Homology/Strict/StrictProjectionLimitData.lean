/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.Functor

/-!
# Strict derived-limit data and diagram postcomposition

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941
(blueprint: def-sbc-strict-projection-tower-data).

The total right derived limit, K-injective computation, evaluation and natural Roos data
are the supplied data of lem-weil-pbc-ringed-strict-tower-homotopy-limit for module sheaves.
This record does not assert existence in an arbitrary abelian category.
`projectionPost` is Mathlib's ordinary diagram postcomposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uI vI uB vB uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace SheafOfModules

end SheafOfModules
