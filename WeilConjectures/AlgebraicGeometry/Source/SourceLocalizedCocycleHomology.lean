/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison

/-! # Evaluation of a localized cocycle on the cohomology sheaf

Source: Stacks Project, Tag 03Q8, computation with an injective complex.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.SourceLocalizedCocycleHomology.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
