/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseComparison

/-! # The normalized comparison on a termwise restricted complex

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-termwise-comparison).

Re-export the adopted source proof at the historical module path. Both paths now
use the same declaration `AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison`.
The historical K-flat spelling `CochainComplex.IsAcyclicTensorKFlat` remains available
through `StalkComparisonPullbackNaturality`; its acyclic tensor formula is definitionally
identical to the source predicate `CochainComplex.IsKFlatTensor`.
-/

@[expose] public section
