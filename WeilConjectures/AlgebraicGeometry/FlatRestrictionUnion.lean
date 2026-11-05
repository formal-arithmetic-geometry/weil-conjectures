/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact

/-! # Flatness on a union of finite locally free loci

Source: blueprint lem-pc-perfect-locus, cohomology-sheaf gluing paragraph.
(blueprint: lem-pc-flat-restriction-union).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
