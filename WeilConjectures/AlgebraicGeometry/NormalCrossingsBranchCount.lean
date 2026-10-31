/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalCrossingsDivisor
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Geometric branch counts of normal crossings divisors

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, 4.1.6 and 4.1.8
(blueprint: def-trf-normal-crossings-branch-count).

The chart predicate uses exactly the local parameter presentation in
`IsNormalCrossingsDivisor`. All its factors are nonunits at the chart point. Thus its
list length counts the factors in the geometric prime. The infimum gives real data
without choosing coordinates or assuming a theorem about coordinate independence.
For a normal crossings divisor the possible lengths form a singleton. Outside that
class the definition is simply a total extension, with the empty-set infimum equal to zero.

## Main definitions

* `HasNCBranchChart` records a pointed etale parameter presentation and its factor count.
* `ncBranchCount` is the coordinate-independent count, encoded by the infimum of the lengths.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A pointed etale parameter presentation with exactly `n` branches through the point.
Unit factors have already been discarded by passing to the local ring.
Source: ILO VIII 4.1.6, 4.1.8 (blueprint: def-trf-normal-crossings-branch-count). -/
def HasNCBranchChart {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) (n : ℕ) : Prop :=
  ∃ (W : Scheme.{u}) (e : W ⟶ X), Etale e ∧
    ∃ (w : W), e w = x ∧
      ∃ (U : W.affineOpens) (hw : w ∈ U.1)
        (hR : IsNoetherianRing (W.presheaf.stalk w))
        (t s : List (W.presheaf.stalk w)),
        @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk w) _ _ hR t ∧
          s.Sublist t ∧ s.length = n ∧
          ((D.comap e).ideal U).map (W.presheaf.germ U.1 w hw).hom =
            Ideal.span {s.prod}

/-- Number of geometric branches through an underlying point, obtained from all pointed
etale normal crossings presentations. For a geometric point `p : Spec Ω ⟶ X` it is
`D.ncBranchCount (p (IsLocalRing.closedPoint Ω))`; it is independent of the chosen
algebraically closed field. The empty product gives zero branches off the divisor.
Source: ILO VIII 4.1.6, 4.1.8 (blueprint: def-trf-normal-crossings-branch-count). -/
def ncBranchCount {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) : ℕ :=
  sInf {n : ℕ | D.HasNCBranchChart x n}

end AlgebraicGeometry.Scheme.IdealSheafData
