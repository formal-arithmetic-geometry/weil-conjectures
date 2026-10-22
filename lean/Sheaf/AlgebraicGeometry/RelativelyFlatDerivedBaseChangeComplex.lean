/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex
public import Sheaf.Algebra.Homology.KFlat

/-! # Derived base change for a bounded relatively flat complex

Compatibility re-export of the adopted source proof of
`AlgebraicGeometry.relativelyFlat_derivedBaseChange_complex`. The source predicate
`IsKFlatTensor` agrees by reduction with the legacy `IsAcyclicTensorKFlat` predicate,
whose import is retained for consumers of the archived signature.

Source: Stacks Project, perfect.tex, Lemma 36.26.4, Tag 0A1D.
(blueprint: lem-pc-rf-base-change-complex).
-/

@[expose] public section
