/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleInjectiveSectionsComparison
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceTransition
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceRestriction
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-sections).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceSections.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
