/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization

/-! # Normalization of the global Hom original counit

Compatibility import for the complete adopted source proof of
the declarations of the former copy (`schemeHomOriginalTensorSpec`,
`schemeHomPullbackCounitIso`, `IsSchemeHomOriginalCounitTensorComparison`, ...).
The source module `WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tags 06YJ and 079U.
(blueprint: lem-pc-global-hom-original-counit-normalization).
-/

@[expose] public section
