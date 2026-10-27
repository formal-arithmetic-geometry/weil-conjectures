/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FanCenterTensorChartData

/-!
# Zariski log structures on saturated blowups of fan centers

Source: ILO VIII 3.3.4--3.3.9, 3.3.12--3.3.13.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- A supplied saturated log blowup of a coherent inverse-image fan center
has a Zariski log structure. No blowup or tensor cover is constructed here.

Source: ILO VIII 3.3.4(ii), 3.3.5--3.3.9, 3.3.12--3.3.13(i),(iii)
(blueprint: lem-trf-fan-center-blowup-zariski).

Proof: Lift the fan chart Zariski locally by `fan_chart_local_monoid_lift`.
The coherent center is generated there by finitely many chart sections.
`coherentLogIdeal_chart_construction` gives saturated fraction-monoid tensor
charts. Their universal property identifies their log blowup with the supplied
one: the unique factorizations in both directions are inverse by uniqueness.
Because the base charts are Zariski opens, the tensor charts are actual opens
of the supplied blowup. Associate the displayed monoid-to-ring chart on the
Zariski site of each tensor spectrum. Its etale association is the given log
structure, by the stalk chart condition, or equivalently by
`monoid_chart_characteristic_fan`. On the intersection of the a and b charts,
localize at b/a and a/b respectively. Both monoids are the same submonoid of
P^gp, and remain equal after saturation, since saturation commutes with
localization. Adjoining inverses of elements mapping to ring units leaves the
associated log structure unchanged. Thus the Zariski log structures agree on
intersections. The identifications come from inclusions in P^gp, hence satisfy
the triple cocycle, and glue. For the stated stalkwise criterion, represent a
geometric characteristic class on a tensor open by a Zariski chart section;
lift equality of characteristic classes by a local ring unit. This is precisely
`IsZariski`. No quasi-compactness of the base is used. -/
theorem fan_center_blowup_zariski
    (V : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u})
    (c : LogFanChart V F) (J : FineFan.IdealFamily F)
    (hJ : FineFan.IsNonemptyCoherentIdeal J)
    (hI : V.logStructure.IsNonemptyCoherentIdeal (c.pullbackIdeal J))
    (V' : FineSaturatedLogScheme.{u}) (b : EtaleLogHom V' V)
    (hb : IsSaturatedLogBlowup b (c.pullbackIdeal J)) :
    V'.logStructure.IsZariski := by sorry

end AlgebraicGeometry
