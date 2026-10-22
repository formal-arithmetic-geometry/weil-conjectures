/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.TensorCounitOneKFlatCoordinates

/-! # Tensor pullback counit in one K-flat coordinate

Compatibility re-export of the adopted, fully proved source theorem
`AlgebraicGeometry.tensorCounit_oneKFlat_coordinates`; this path is retained for the
Sheaf namespace mirror after the quarantine rework. The source K-flat predicate
`IsKFlatTensor` agrees by reduction with the legacy `IsAcyclicTensorKFlat` predicate.
The canonical comparison import preserves the legacy statement vocabulary.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates).
-/

@[expose] public section
