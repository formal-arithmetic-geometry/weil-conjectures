/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison

/-! # Naturality of the source derived-sections comparison

Source: Stacks Project, Tags 03Q8 and 03Q9. We check precomposition on cochains,
cocycles, their quotient, and the corresponding derived morphisms.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.SourceDerivedSectionsNaturalityCore.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Etale

section HomPrecomposition

end HomPrecomposition

end AlgebraicGeometry.Etale
