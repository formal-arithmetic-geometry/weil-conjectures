/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.AlgebraicGeometry.FanChartStalkModel

/-!
# Detecting a log chart by its characteristic fan morphism

Source: ILO VI 1.1 and VIII 3.1.4(iii), 3.1.8(ii), 3.3.12.
(blueprint: lem-trf-fan-chart-section-is-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Lifting the full characteristic fan morphism by sections gives a log chart.
Only the factorization and characteristic-section identities are needed; no choice
of a section of a group completion is involved.

Source: ILO VI 1.1, p.69; VIII 3.1.4(iii), 3.1.8(ii), pp.98--99; 3.3.12, p.108
(blueprint: lem-trf-fan-chart-section-is-chart).

Proof: Fix a geometric point over y in U and let E be the face of monoid elements
whose images under alpha h are units in its strict local ring B. The equality of
sharp germs and the factorization through c identify its characteristic monoid with
Associates (P localized at E), by affine fan localization. Zariski unit extension
identifies this with the actual geometric characteristic of N. The associated-log
stalk is the pushout P plus_E B^units and its map to N sends [p,u] to h(p)u.
This map is surjective: every characteristic is represented by p/e, and h(e) is a
unit, so the denominator can be absorbed in u. For injectivity, if h(p)u=h(p')u',
then equality in the localized sharp monoid gives e,e' in E with p*e'=p'*e.
Cancellation in the integral geometric log stalk gives u*h(e)=u'*h(e').
The pushout relations therefore identify [p,u] and [p',u']. Its kernel congruence
is exactly the defining pushout congruence. Surjectivity and that kernel equality
are IsStalkChart, at every geometric point; these are precisely IsChart. The
trivial monoid and the case that every generator becomes a unit are included. -/
theorem fan_chart_section_is_chart
    {X : FineSaturatedLogScheme.{u}} {F : FineFan.Fan.{u}}
    (c : LogFanChart X F) (x : X.scheme)
    (L : FineFan.PointLocalization F (c.map.hom.base x))
    (hP : IsFineSaturatedMonoid
      (FineFan.stalk F.space.presheaf (c.map.hom.base x)))
    (U : X.scheme.Opens)
    (h : FineFan.stalk F.space.presheaf (c.map.hom.base x) →*
      X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj U)))
    (a : X.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶
      F.space.restrict L.openSet.isOpenEmbedding)
    (ha : a ≫ F.space.ofRestrict L.openSet.isOpenEmbedding =
      X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ c.map)
    (hh : ∀ (p : FineFan.stalk F.space.presheaf (c.map.hom.base x))
      (y : X.scheme) (hy : y ∈ U),
      FineFan.stalkMap (X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding)
          ⟨y, hy⟩ (FineFan.germ X.logStructure.sharpSpace.presheaf U y hy
            (X.logStructure.sharpSection U (h p))) =
        FineFan.germ (X.logStructure.sharpSpace.restrict U.isOpenEmbedding).presheaf
          ⊤ ⟨y, hy⟩ (by trivial) (FineFan.affinePullback (a ≫ L.iso.hom) p)) :
    X.logStructure.IsChart ((logOpenEtale X.scheme).obj U) h := by
  sorry

end AlgebraicGeometry
