/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit

/-! # Unit laws for derived pullback tensor comparisons

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.derivedPullback_tensor_unit`. The source theorem supplies the
unit isomorphism and both unit laws, without assuming associativity. Its
`CochainComplex.IsKFlatTensor` is the acyclic-tensor predicate formerly named
`CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit).
-/

@[expose] public section
