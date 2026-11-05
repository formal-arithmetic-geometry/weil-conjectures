/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Finite local models for a locally free coefficient line

Source: Stacks Project, Tag 03RV; coefficient-twist blueprint, proof steps 1 and 8.
(blueprint: lem-pur-finite-locally-free-line-models)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
