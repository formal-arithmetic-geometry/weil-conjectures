/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Canonical open pullback and restricted coefficient data

Source: Stacks Project, Tag 0DJ9, first paragraph; Tag 08HY, counit description.
(blueprint: def-pc-single-complex-open-restriction-data).

These are the unchanged constructions formerly in SingleComplexOpenRestrictionComparison.
They are isolated here so independent compatibility calculations can import them without a cycle.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
