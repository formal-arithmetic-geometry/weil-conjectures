/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.FlatRestrictionUnion
import WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology
import WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # The flat single-cohomology open locus

Source: the cohomology-sheaf gluing paragraph of the perfect-locus proof
(blueprint: lem-pc-derived-single-open-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
