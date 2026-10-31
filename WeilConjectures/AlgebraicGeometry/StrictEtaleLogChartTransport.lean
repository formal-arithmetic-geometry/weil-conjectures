/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FSLogSmoothEtale
public import WeilConjectures.AlgebraicGeometry.FSStrictLogMorphism
/-!
# Transport of compatible fs charts along strict etale neighbourhoods
Source: ILO VI 1.1, VIII 3.3.4(ii), X 1.2
(blueprint: lem-sfb-strict-etale-log-chart-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Compatible charts can be transported in either direction across strict etale
source and target neighbourhoods at each point. The assertions concern one point,
so no global covering assumption is imposed.
Source: ILO VI 1.1, VIII 3.3.4(ii), X 1.2
(blueprint: lem-sfb-strict-etale-log-chart-transport).

Proof: in the descent direction concatenate the chart neighbourhoods with the
strict etale maps a and b. Strictness identifies the chart log structures on the
composites with the prescribed log structures. The monoid map, kernel and cokernel
are unchanged. The comparison is obtained by etale composition, so it retains
smoothness or etaleness. In the ascent direction pull back the target chart along
b and then pull back the source chart along a to a neighbourhood of the given
point. The map from the resulting source neighbourhood to the pulled-back source
chart is etale: the two maps are etale over X and etale cancellation applies.
Strictness identifies their charts; the comparison is an etale map followed by a
base change of the old comparison. Smooth and etale morphisms are stable under
base change and etale composition. Kernel and cokernel order conditions persist
under local ring maps. Refine the neighbourhood if necessary to lift the target
chart point. This proves both directions for each chart predicate. Empty schemes
cause no extra case because the statement quantifies over an actual source point. -/
theorem strictEtale_logChart_transport
    {X Y U V : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    (a : EtaleLogHom U X) (b : EtaleLogHom V Y) (r : EtaleLogHom U V)
    (c : EtaleLogHom U Y) (ha : a.IsStrict) (hea : Etale a.base)
    (hb : b.IsStrict) (heb : Etale b.base)
    (haf : a.CompEq f c) (hrb : r.CompEq b c) (z : U.scheme) :
    ((∃ d : FSLogChart f, a.base z ∈ Set.range d.V.hom ∧ d.IsSmoothChart) ↔
      ∃ d : FSLogChart r, z ∈ Set.range d.V.hom ∧ d.IsSmoothChart) ∧
    ((∃ d : FSLogChart f, a.base z ∈ Set.range d.V.hom ∧ d.IsEtaleChart) ↔
      ∃ d : FSLogChart r, z ∈ Set.range d.V.hom ∧ d.IsEtaleChart) := by
  sorry
end AlgebraicGeometry
