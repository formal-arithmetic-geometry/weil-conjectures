/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleInjectiveSectionsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Canonical cycle comparisons for source sections

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

section
variable {C : Type (v + 1)} [Category.{v} C]
  {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]

end

end AlgebraicGeometry.Etale
