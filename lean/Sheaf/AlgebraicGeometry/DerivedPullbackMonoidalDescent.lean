/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent

/-! # Descent of coherent tensor pullback comparisons

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.derivedPullback_monoidal_descent`.
The source module `WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-monoidal-descent).
-/

@[expose] public section
