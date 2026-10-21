/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineMorphismHomOutOfPerfect

/-! # Hom out of a perfect complex along an affine morphism

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.affineMorphism_hom_out_of_perfect`.
The source module `WeilConjectures.AlgebraicGeometry.AffineMorphismHomOutOfPerfect` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, perfect.tex, lemma-affine-morphism-and-hom-out-of-perfect,
case (1) (blueprint: lem-pc-affine-morphism-hom-out-of-perfect).
-/

@[expose] public section
