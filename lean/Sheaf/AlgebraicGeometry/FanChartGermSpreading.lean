/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.AlgebraicGeometry.FanChartStalkModel

/-!
# Spreading a characteristic monoid section from an ordinary stalk

Source: ILO VI 3.7(a), p.75; VIII proof of 3.3.15, p.109.
(blueprint: lem-trf-fan-chart-germ-spreading).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A section of the characteristic quotient at one ordinary stalk extends to a
homomorphism of sections, with precisely the prescribed characteristic fan morphism.
This statement asserts no log-chart property.

Source: ILO VI 3.7(a), p.75; VIII proof of 3.3.15, p.109
(blueprint: lem-trf-fan-chart-germ-spreading).

Proof: In the inverse image of L.openSet, pull back the canonical sections of the
localized fan using c. At x their germs are identified with the fan stalk by the
normalization of L and the chart stalk isomorphism. Choose finitely many generators
of that fine stalk and a finite relation presentation. Represent the finitely many
images under j by log sections on a common neighborhood of x in this inverse image.
Every defining relation is true at x, hence true on a smaller neighborhood. Intersect
these finitely many neighborhoods; the presentation gives h with germ j. On each
generator its sharp section and the prescribed characteristic section have equal
germs, by the section hypothesis on j. Shrink again for these finitely many equalities.
The resulting homomorphisms agree on all elements. Restrict the original fan morphism
to this neighborhood and its image open to obtain a; its factorization is built into
the restriction. Naturality of germs gives the equality at every restricted stalk.
Empty tuples of generators or relations require no shrinking. -/
theorem fan_chart_germ_spreading
    {X : FineSaturatedLogScheme.{u}} {F : FineFan.Fan.{u}}
    (c : LogFanChart X F) (x : X.scheme)
    (L : FineFan.PointLocalization F (c.map.hom.base x))
    (j : FineFan.stalk F.space.presheaf (c.map.hom.base x) →*
      FineFan.stalk X.logStructure.zariskiPresheaf x)
    (hj : ∀ p, c.stalkQuotient x (j p) = p) :
        ∃ (U : X.scheme.Opens) (hx : x ∈ U)
          (h : FineFan.stalk F.space.presheaf (c.map.hom.base x) →*
            X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj U)))
          (a : X.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶
            F.space.restrict L.openSet.isOpenEmbedding),
          (∀ y ∈ U, c.map.hom.base y ∈ L.openSet) ∧
          a ≫ F.space.ofRestrict L.openSet.isOpenEmbedding =
            X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ c.map ∧
          (∀ (p : FineFan.stalk F.space.presheaf (c.map.hom.base x))
            (y : X.scheme) (hy : y ∈ U),
            FineFan.stalkMap (X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding)
                ⟨y, hy⟩ (FineFan.germ X.logStructure.sharpSpace.presheaf U y hy
                  (X.logStructure.sharpSection U (h p))) =
              FineFan.germ (X.logStructure.sharpSpace.restrict U.isOpenEmbedding).presheaf
                ⊤ ⟨y, hy⟩ (by trivial) (FineFan.affinePullback (a ≫ L.iso.hom) p)) ∧
          ∀ p : FineFan.stalk F.space.presheaf (c.map.hom.base x),
            FineFan.germ X.logStructure.zariskiPresheaf U x hx (h p) = j p := by
  sorry

end AlgebraicGeometry
