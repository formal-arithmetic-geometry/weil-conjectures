/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat
public import Sheaf.Algebra.Homology.KFlat

/-! # Tensor compatibility of derived pullback composition on K-flat complexes

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat`. Its hypotheses use
`CochainComplex.IsKFlatTensor`, definitionally equal to the archived
`CochainComplex.IsAcyclicTensorKFlat`. The legacy predicate remains publicly
available, so the unchanged archived statement can use the source theorem directly.
The selected composition comparison and tensorators are identical.

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-tensor-kflat).
-/

@[expose] public section
