/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.Curve.MateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit

/-! # The strict-local base-change mate on global cohomology

This theorem retains `strictHenselizationScheme` and its structural map.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tags 03Q8, 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
