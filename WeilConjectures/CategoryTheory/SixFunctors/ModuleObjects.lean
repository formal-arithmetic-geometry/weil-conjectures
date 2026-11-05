/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Module objects in a monoidal category

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sfb-module-objects
(blueprint: sk-def-sfb-module-objects).

For a monoid object `R` in a monoidal category `C`, `CategoryTheory.Mod C R` is
Mathlib's category of left `R`-module objects.  Its objects carry an action
`R ⊗ M ⟶ M` with the unit and associativity laws, and its morphisms are the
maps commuting with the actions.  The regular module is supplied by
`CategoryTheory.Mod.regular`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

end AlgebraicGeometry.ProEtale
