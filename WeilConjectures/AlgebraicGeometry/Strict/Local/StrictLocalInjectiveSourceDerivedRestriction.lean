/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalComplexSectionsMate
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalLocalizedHomGerm

/-! # The derived mate on a neighbourhood germ -/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
