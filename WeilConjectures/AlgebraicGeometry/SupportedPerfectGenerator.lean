/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated

/-! # Perfect generators with support

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.15.4 (Tag 0A9A)
(blueprint: lem-pc-supported-perfect-generator).

Support on `T` is the stalkwise form of the existing support statements: every cohomology
sheaf has zero stalk at every point outside `T`. `D_QCoh,T(O_X)` is the full subcategory
of `D(O_X)` on objects with quasi-coherent cohomology supported on `T`. The weak generator
condition (`def-pc-generators`) is expressed by the shifted-Hom vanishing criterion, as in
`AlgebraicGeometry.perfect_generator_pullback`; Hom groups and shifts of the full
subcategory are those of the ambient derived category.
-/
