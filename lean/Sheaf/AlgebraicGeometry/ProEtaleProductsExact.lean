/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Exact products of pro-etale module sheaves

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-prop-pe-products/det-pe-products-exact.md
(blueprint: det-pe-products-exact).
-/

@[expose] public section

set_option autoImplicit false

universe t u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every set-indexed product functor on modules over a pro-etale ring sheaf is exact.
`HasExactLimitsOfShape (Discrete I)` asserts right exactness of the product functor;
its left exactness follows because it is a limit functor. Thus this says that the
product of any family of short exact sequences is short exact, including both endpoints.
The module universe contains the site and the indexing set.

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-prop-pe-products/det-pe-products-exact.md
(blueprint: det-pe-products-exact).

Proof: Evaluate at an affine weakly contractible object W. Evaluation commutes with
products by det-pe-sections-limits-colimits, and det-pe-wc-sections-exact makes each
evaluated sequence short exact. The product of these module sequences is exact:
injectivity and equality of image and kernel are coordinatewise, and choice supplies
a preimage in every coordinate of any tuple in the target. Therefore the product
sequence is exact after evaluation at every such W. Apply det-pe-sections-conservative
to detect exactness at its middle term and, using zero terms, at both endpoints.
This is exactness of the product functor. -/
theorem products_exact (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u w (t + 1)}) (I : Type w) :
    HasExactLimitsOfShape (Discrete I) (SheafOfModules.{max u w (t + 1)} R) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
