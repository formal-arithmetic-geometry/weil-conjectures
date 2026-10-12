/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleSupport
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Independence of the geometric point in étale sheaf support

Source: the Weil conjectures blueprint, `sec-smooth-purity`,
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-support-geometric-point-independent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Two geometric points over the same point of a scheme have simultaneously zero stalks
for every étale sheaf of abelian groups. Consequently, the condition defining membership
in the support of such a sheaf is independent of the geometric point chosen over that point.

Source: Weil conjectures blueprint, `sk-prop-sf-kunneth-ordinary`, node
`lem-kun-support-geometric-point-independent`.
(blueprint: lem-kun-support-geometric-point-independent)

Proof: Embed a separable closure of the common residue field in both algebraically closed
geometric-point fields, and factor both points through its spectrum. Pull the sheaf back to
that spectrum. The inverse-image stalk comparison identifies the two original stalks with
stalks of the pullback. The separable closure is strictly henselian, so both stalks of the
pullback identify with its global sections. They are therefore simultaneously zero, and the
definition of support by a nonzero geometric stalk gives the final assertion. -/
theorem isZero_sheafFiber_iff_of_same_image {X : Scheme.{u}}
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X)
    (h : s default = s' default) (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsZero ((pointSmallEtale s).sheafFiber.obj F) ↔
      IsZero ((pointSmallEtale s').sheafFiber.obj F) := by
  sorry

end AlgebraicGeometry.Scheme
