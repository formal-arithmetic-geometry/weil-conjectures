/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedEquivariantBarData

/-! # The bundled all-continuous scalar ring

Source: main-20261015 blueprint, continuous-map condensed rings and direct-images
proof paragraph (3) (blueprint: def-sfb-bundled-continuous-scalar-ring).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Profinite.CondensedAction

/-- Bundle the recorded all-continuous scalar sheaf and its canonical ring structure.
All three fields use the recorded continuous-map constructions; no new sheaf or
multiplication is introduced.
Source: main-20261015 continuous-map condensed ring, last sentence
(blueprint: def-sfb-bundled-continuous-scalar-ring). -/
def continuousScalarRing (F : Type u) [TopologicalSpace F] [CommRing F]
    [IsTopologicalRing F] : CategoryTheory.CondensedBar.Ring.{u} :=
  { X := Profinite.continuousMapRingObjOfUniverse.{u, u} F
    mon := Profinite.continuousMapRingObjOfUniverseMonObj F
    comm := Profinite.isCommMonObj_continuousMapRingObjOfUniverse F }

end Profinite.CondensedAction
