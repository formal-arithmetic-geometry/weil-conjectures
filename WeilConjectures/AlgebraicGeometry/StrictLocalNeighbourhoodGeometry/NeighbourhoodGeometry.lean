/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison

/-! # Canonical neighbourhood geometry on the small colimit model

Transport upstream's geometry along the canonical spectrum-colimit isomorphism.
Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

namespace StrictLocalNeighbourhoodGeometry

end StrictLocalNeighbourhoodGeometry
end AlgebraicGeometry.Etale
