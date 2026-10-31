/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerBoundedTransport
/-! # Geometric transport data -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
/-- The geometric core before the transported counit and Hom equivalence are adjoined.
This is the original geometric transport record, without another copy of its fields.
Normalization of the finite evaluation is imposed by the core existence theorem.
Source: Zheng Lemmas 4.10, 5.16 and 5.22; geometric transport plan Steps 2--10.
(blueprint: def-route-brown-geometric-transport-core). -/
abbrev GeometricTransportCore (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G) :=
  GeometricTransport S G H

end BrownTowerComparison
end AlgebraicGeometry
