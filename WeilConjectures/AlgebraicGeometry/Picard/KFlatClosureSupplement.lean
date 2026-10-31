/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.KFlatClosure

/-!
# Closure of K-flat complexes under countable sums and cones

Source: Stacks Project, Cohomology on Sites, Lemmas 06YR and 07A3
(blueprint: lem-pc-kflat-cone-direct-sum).

The two closure statements are upstream's `CochainComplex.isKFlat_coproduct_nat` and
`CochainComplex.isKFlat_mappingCone` of `WeilConjectures.Algebra.Homology.KFlatClosure`; this module
re-exports them together with the legacy predicate `CochainComplex.IsAcyclicTensorKFlat`, which unfolds
to upstream's `CochainComplex.IsKFlatTensor`. Our copy of the two theorems was removed on 2026-10-30:
it declared the same names, so a module importing both failed.
-/
