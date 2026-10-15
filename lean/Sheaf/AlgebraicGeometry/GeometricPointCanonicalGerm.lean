/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk
public import Sheaf.AlgebraicGeometry.DerivedGlobalGerm
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-!
# The canonical germ at the identity geometric point

Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3)
(blueprint: lem-weil-pbc-geometric-point-pullback-stalk).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical global germ on the spectrum of an algebraically closed field is invertible.
Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3)
(blueprint: lem-weil-pbc-geometric-point-pullback-stalk).
Proof: every pointed étale neighbourhood of the identity point has its specified section
through that point. Restricting along this section sends its germs to global sections.
The stalk colimit relations make this independent of the neighbourhood and inverse to
`globalGerm`. Equivalently apply the strictly henselian sections-to-stalk theorem to the
algebraically closed field and its identity point. This identifies the specific germ map,
not just an unspecified isomorphism of the two functors. Naturality is the naturality of
`globalGerm`. The original equivalence and module clauses remain publicly imported. -/
theorem isIso_globalGerm_identity (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    IsIso (globalGerm (𝟙 (Spec (.of Ω)))) := by
  sorry

end AlgebraicGeometry.Etale
