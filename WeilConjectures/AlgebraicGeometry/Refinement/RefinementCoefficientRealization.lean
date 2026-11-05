/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The finite coefficient realization interface for refinement comparisons

Source: blueprint finite coefficient modules, order 1233; module sheafification along
locally bijective constant scalars (blueprint: def-weil-pbc-proetale-modules).

The recorded finite-module definitions are reexported. This exposes coefficient realization
without importing the second copy of the fixed-coefficient six-functor declarations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
