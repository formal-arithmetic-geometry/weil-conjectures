/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.ImageFiltration
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.TruncationRawExact
import WeilConjectures.CategoryTheory.TruncationQuadrantVanishing
import WeilConjectures.CategoryTheory.HalfPlaneSharpBounds
import WeilConjectures.CategoryTheory.TruncationCanonicalAbutment

/-!
# The truncation hypercohomology spectral sequence

Source: Weil conjectures blueprint, sec-proper-base-change, sk-thm-properbasechange,
node thm-sp-truncation-e2, order 1212; Stacks Project, Tags 015J, 05TC, 011Q,
011R, 011T, 0BDU, 0BDV and 012U (blueprint: thm-sp-truncation-e2).

The integer `a` is a cohomological lower bound, not a bound on the terms of `K`.
The natural index of `pageCouple` and of the cycle/boundary tower is the page minus two.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

end CategoryTheory
