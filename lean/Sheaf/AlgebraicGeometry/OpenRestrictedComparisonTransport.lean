/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport

/-! # Comparison on the literal restriction of a complex

Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9.
(blueprint: lem-pc-open-restricted-comparison-transport).

Re-export the adopted source proof at the historical module path. Its K-flat
predicate `IsKFlatTensor` has the same defining acyclic-test-complex formula as
`IsAcyclicTensorKFlat`, retained through the public naturality import. The
comparison maps, representative data and derived-composition transport agree.
-/

@[expose] public section
