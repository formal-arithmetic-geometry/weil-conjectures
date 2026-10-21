/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization

/-! # Normalization of the successive tensor pullback route

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.derivedPullback_tensor_successive_normalization`.
The source uses `CochainComplex.IsKFlatTensor` for the same acyclic-tensor
condition formerly named `CochainComplex.IsAcyclicTensorKFlat` here. All the
remaining hypotheses, chosen comparisons, counits, and the normalization
identity are identical. Reusing that proof avoids a second declaration of the
same theorem and retains the normalization theorem at this import path.

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-tensor-successive-normalization).
-/

@[expose] public section
