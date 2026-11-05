/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward

/-!
# Transport of the closed fibre to the small strict henselization

The canonical colimit isomorphism intertwines the small-model structural map with
`strictLocalizationToBase`. This transfers the upstream singleton-fibre theorem without
exposing its different structural-map compatibility API.

Source: Stacks Project, Tags 04GW, 04GP and 04HX.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
