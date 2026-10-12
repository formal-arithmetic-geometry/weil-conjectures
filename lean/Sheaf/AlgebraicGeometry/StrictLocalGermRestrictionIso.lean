/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # The strict-local germ restriction is an isomorphism

Source: Stacks Project, Tags 03QO and 03Q9.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical germ restriction identifies a geometric stalk with strict-local sections.
Source: Stacks Project, Tag 03QO and the restriction construction of Tag 03Q9
(blueprint: lem-weil-pbc-strict-local-germ-restriction-iso).

Proof: choose an affine chart containing the image of `s`. The comparison
`lem-weil-pbc-etale-local-ring-triples` identifies the chosen coordinate-ring colimit with
that of étale residue triples over this chart, compatibly with every pointed ring map.
`lem-weil-pbc-strict-henselization-triples` makes the latter strictly henselian local and
identifies its residue field with the relative separable closure inside Ω. Transport the
local-ring structure through the colimit isomorphism and compose its residue map with the
inclusion into Ω. This gives the distinguished geometric closed point of the chosen
strict-local scheme above `s`, with the required equality after the structural map.
The inverse-image stalk comparison identifies the stalk of the pulled-back sheaf
there with the original stalk. On a strictly henselian local scheme, every pointed étale
neighbourhood of the closed point admits a section: shrink it to an affine neighbourhood,
then split its étale algebra into the factor containing that point and its complement.
Consequently evaluation at the identity neighbourhood computes this stalk, and the global
sections-to-stalk map is an isomorphism (03QO). Compose its inverse with the inverse-image
stalk comparison. On a representative neighbourhood its composite with the germ is the
adjunction unit followed by restriction along the strict-local limit leg. These are precisely
`strictHenselizationSectionRestriction`, so uniqueness of the germ restriction identifies
this isomorphism with `r`.
-/
theorem isIso_strictHenselizationStalkRestriction
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj G))
    (hr : IsStrictHenselizationStalkRestriction s G r) : IsIso r := by
  sorry

end AlgebraicGeometry.Etale
