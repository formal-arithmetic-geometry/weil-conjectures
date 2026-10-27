/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.AlgebraicGeometry.ConductorResolutionTower

/-! # Canonical comparisons for conductor-prepended towers

Source: ILO VIII 2.2.7--2.2.9 and 2.3.4--2.3.5(i).
(blueprint: lem-trf-conductor-resolution-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth map has a conductor-extended comparison, unique on the ordered indices
and actual maps of surviving levels. The auxiliary models of the pulled tower may
vary, but all data used by the resulting resolution rule is characterized uniquely.
Source: ILO VIII 2.2.7--2.2.9 and 2.3.4, conductor-prepending refinement.
(blueprint: lem-trf-conductor-resolution-comparison).

Proof: use rationalConductor_smoothBaseChange to get the unique smooth map between
normal preparations and apply N.comparison to it. If the target conductor is unit,
so is its pullback and both towers are rebased tails. If both conductors are nonunit,
prepend the cartesian conductor square to that comparison. If only the source
conductor is unit, prepend the unit normalized blowup over the normal source to the
pulled tower, and delete this isomorphism before the tail's ordered contraction.
At each tail level use the pullback square in N.comparison and extend the identical
center. Shift the retained indices by the conductor stage counts. The three cases
give all base, arrow, center, cartesian and contraction equations, with no change of
order. To check uniqueness, the unit/nonunit ideals determine the contraction index
recursively from zero. At retained levels the map is determined over the dense
complement of the preceding centers, where every tower arrow is an isomorphism;
reducedness and separatedness of each normalized blowup over its base extend this
equality across the whole level. This proves HEq of the actual maps after the unique
index identifications. Empty schemes, length-zero tails and proper invertible centers
are included; a proper invertible center is retained despite its isomorphism arrow. -/
theorem rationalConductorTower_comparison
    (N : SmoothNormalizedResolutionRule NormalRationalResolutionInput.{u}
      (fun X ↦ X.val.scheme))
    (X Y : RationalResolutionInput.{u}) (h : Y.scheme ⟶ X.scheme) (hh : Smooth h) :
    ∃ c : QENormalizedResolutionComparison h
      (rationalConductorTower X (N.tower (normalConductorPreparedRationalInput X)))
      (rationalConductorTower Y (N.tower (normalConductorPreparedRationalInput Y))),
      ∀ d : QENormalizedResolutionComparison h
        (rationalConductorTower X (N.tower (normalConductorPreparedRationalInput X)))
        (rationalConductorTower Y (N.tower (normalConductorPreparedRationalInput Y))),
        (∀ i, d.contraction.index i = c.contraction.index i) ∧
          (∀ i, HEq (d.levelMap i) (c.levelMap i)) := by sorry

end AlgebraicGeometry
