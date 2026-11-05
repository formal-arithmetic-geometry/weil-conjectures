/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exact.ExactGlobalSectionsLeray
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Projection data for the small coordinate-ring colimit model

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.

The target is `strictHenselizationScheme s`. The adopted names in
`WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionData` use
`strictLocalization s`; the explicit small-model names here keep the two APIs distinct.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
