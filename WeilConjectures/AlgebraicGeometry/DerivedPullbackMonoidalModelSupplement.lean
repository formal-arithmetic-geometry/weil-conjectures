/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel

/-! # Monoidal models of the derived pullback

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.IsDerivedPullbackMonoidalModel` and
`AlgebraicGeometry.exists_derivedPullbackMonoidalModel`.
The source module `WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: def-pc-derived-pullback-monoidal-model).
-/

@[expose] public section
