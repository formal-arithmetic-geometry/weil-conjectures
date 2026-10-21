/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization

/-! # Factorization of the affine global Hom base change map

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.affineGlobalHomBaseChange_factorization`.
The source module `WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, perfect.tex, Tag 0AA7,
lemma-affine-morphism-and-hom-out-of-perfect, case (1); cohomology.tex, Tag 08I3.
(blueprint: lem-pc-affine-global-hom-base-change-factorization).
-/

@[expose] public section
