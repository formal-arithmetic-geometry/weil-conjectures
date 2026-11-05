/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisComparisons
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisExact

/-!
# Mayer-Vietoris for étale cohomology

Source: Stacks Project, Étale Cohomology, Tag 0A50, and Cohomology on Sites,
Tag 03F3 (2) (blueprint: lem-weil-pbc-etale-mayer-vietoris).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
