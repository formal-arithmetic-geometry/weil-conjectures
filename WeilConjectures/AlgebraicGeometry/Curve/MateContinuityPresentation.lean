/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalCohomologySourceColimit
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalMateProjectionFormulas

/-! # Projection-restriction presentation on the small strict-local model

This theorem uses `strictHenselizationScheme` and `strictHenselizationStructuralMap`.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tag 03Q9, the neighbourhood-colimit construction and the
injective-complex restriction maps in its final proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
