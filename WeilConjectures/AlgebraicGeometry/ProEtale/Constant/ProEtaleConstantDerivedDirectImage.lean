/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleDirectImageLeftExact

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!
# Canonical constant-coefficient derived direct image

Source: Weil conjectures blueprint, `def-weil-derived-direct-image`, order 1468;
Stacks Project, Cohomology on Sites, Section 07A5
(blueprint: def-weil-pbc-proetale-operations).

The canonical constant-section structure map already defines module direct image.
Its right derived functor needs no separately supplied coefficient identification.
All the recorded identified-coefficient operations are reexported.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
