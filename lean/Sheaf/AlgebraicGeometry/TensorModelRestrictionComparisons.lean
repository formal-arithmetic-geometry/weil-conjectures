/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.TensorModelRestrictionComparisons

/-! # Coherent tensor-model comparisons under open restriction

The upstream theorem `AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons`
is re-exported here. Its `CochainComplex.IsKFlatTensor` hypothesis is definitionally equal to
`CochainComplex.IsAcyclicTensorKFlat`, so existing callers retain the same proposition.
Keeping one declaration also permits importing this module together with its upstream version.

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DL and 06YH.
(blueprint: lem-sc-tensor-model-restriction-comparisons).
-/

@[expose] public section
