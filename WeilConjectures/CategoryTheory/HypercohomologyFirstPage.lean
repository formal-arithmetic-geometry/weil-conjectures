/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.CartanEilenbergSecondFiltration
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-! # The first hypercohomology spectral sequence

Source: Stacks Project, Tags 0130 and 015H; blueprint order 522
(blueprint: thm-sp-if-e1).

The bicomplex uses the Stacks order (complex degree, resolution degree); flipping after
extension by zero gives the order (resolution degree, complex degree) of the blueprint.
The spectral sequence uses Mathlib's order (filtration degree, complementary degree).
Thus the blueprint term E₁^{r,s} is `(E.page 1).X (s,r)` here. Signed identifications
with the derived functors absorb the second-filtration sign in Tag 0130.
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

end CategoryTheory.Functor
