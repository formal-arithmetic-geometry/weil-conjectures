/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat

/-! # Unit laws on K-flat representatives

The adopted source module provides `AlgebraicGeometry.derivedPullback_tensor_unit_kFlat`
and its complete proof. This compatibility import preserves access through the Sheaf path
without importing a second construction of derived pullback. Its K-flat hypothesis uses
`CochainComplex.IsKFlatTensor`, the same acyclic-tensor predicate as the former
`CochainComplex.IsAcyclicTensorKFlat`.

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit-kflat-coherence).
-/

@[expose] public section
