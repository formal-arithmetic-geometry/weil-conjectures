/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.CechComparisonMapNaturality

/-! # Naturality of the first Čech-to-cohomology comparison

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ
(blueprint: lem-sc-cech-h1-map-natural).

The canonical comparison is characterized by the existing `IsModuleCechComparison`
predicate, so its existence cannot be witnessed by an arbitrary natural homomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
