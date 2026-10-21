/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

/-! # The affine global Hom base change map

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.affineGlobalHomBaseChangeMap` and its companions; the source
dropped the perfectness and quasi-coherence hypotheses of `globalHomPullbackComparison`.
The source module `WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, perfect.tex, Tag 0AA7 (blueprint:
def-pc-affine-global-hom-base-change-map).
-/

@[expose] public section
