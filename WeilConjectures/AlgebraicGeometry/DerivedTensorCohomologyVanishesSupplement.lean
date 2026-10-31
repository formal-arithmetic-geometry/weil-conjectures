/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Vanishing of derived tensor cohomology on a scheme

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU;
Derived Categories of Schemes, Tag 08EA
(blueprint: def-pc-derived-tensor-cohomology-vanishes).
-/

-- The adopted source module declares the same predicate. Reexport it so that
-- clients of the two module paths use one definition of derived tensor vanishing.
