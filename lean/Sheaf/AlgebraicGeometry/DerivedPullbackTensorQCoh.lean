/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Derived pullback and tensor preserve quasi-coherent cohomology

The adopted source library provides `AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh`.
This module re-exports that theorem without redeclaring it. Its K-flat predicate
`CochainComplex.IsKFlatTensor` is the same acyclic-total-tensor condition as the former
`CochainComplex.IsAcyclicTensorKFlat` predicate.

Source: Stacks Project, Derived Categories of Schemes, Tags 08DW(1) and 08DX(1).
(blueprint: lem-pc-derived-pullback-tensor-qcoh).
-/

@[expose] public section
