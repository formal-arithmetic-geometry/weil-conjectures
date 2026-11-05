/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Derived categories on an open subscheme

For an open `U` of `X`, derived categories of `𝒪_U`-modules and of modules on the localized
sites of `U`, in the universe of the derived categories given on `X`.
Source: Stacks Project, Tag 079W.
(blueprint: lem-pc-open-derived-localization-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

end AlgebraicGeometry
