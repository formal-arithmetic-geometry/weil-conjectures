/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceSections
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # Projection restriction formulas for the strict-local mate

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
