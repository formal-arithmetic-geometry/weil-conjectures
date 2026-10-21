/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # The canonical pullback tensor comparison

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.IsCanonicalPullbackTensorComparison`,
`AlgebraicGeometry.exists_canonicalPullbackTensorComparison` and their companions.
The source module `WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison).
The comparison is the unique family satisfying `IsCanonicalPullbackTensorComparison`:
it is pinned by the actual module pullback tensor map and the shared left-derived
counit on K-flat representatives. Statements bind the comparison together with this
uniquely characterising predicate; no monoidal structure on pullback is chosen
arbitrarily and no data is chosen from a theorem.
-/

@[expose] public section
