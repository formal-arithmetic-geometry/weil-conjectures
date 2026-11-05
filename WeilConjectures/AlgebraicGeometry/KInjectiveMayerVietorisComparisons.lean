/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction

/-! # Derived comparisons for the fixed open direct-image complexes

Source: Stacks Project, Cohomology, Tag 08BV, K-injective computation of
open direct image; Tag 08BS, preservation of K-injectivity by restriction.
(blueprint: lem-pc-kinjective-mayer-vietoris-comparisons).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
