/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar

/-!
# Derived coefficient change of supported Kummer classes

Source: Stacks Project, Tag 07A6; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md, final paragraph
(blueprint: def-asd-ordinary-supported-kummer-scalar).

## Main definitions

* `SupportedDerivedScalarUnit`: the derived scalar-unit universal property.
* `SupportedKummerScalar`: the normalized scalar-extension square for the classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

end AlgebraicGeometry.Etale
