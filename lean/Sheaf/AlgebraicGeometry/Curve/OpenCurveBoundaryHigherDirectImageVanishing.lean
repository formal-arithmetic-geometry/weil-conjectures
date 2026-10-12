/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.Curve.BrauerAlgebraicExtension
import Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Higher direct images of the multiplicative group across a curve boundary

Source: Stacks Project, discussion preceding Tag 03RM and the geometric-stalk calculation
of Tag 03RJ, adapted to the complement of finitely many closed points
(blueprint: lem-sc-open-curve-boundary-higher-direct-image-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For the inclusion of the complement of a finite set of closed points in a proper smooth
connected curve over an algebraically closed field, the geometric stalks of the first and
second higher direct images of `G_m` vanish.
Source: Stacks Project, discussion preceding Tag 03RM; Tag 03RJ's stalk calculation
(blueprint: lem-sc-open-curve-boundary-higher-direct-image-vanishing).

Proof:
1. The curve is Noetherian by `lem-sc-smooth-connected-curve-local-rings`. Thus its open
   immersion is quasi-compact and quasi-separated. Apply
   `lem-weil-pbc-gm-strict-henselization-stalk-formula` (Tag 03Q9): the stalk is the etale
   cohomology of `G_m` on the pullback of the open curve to the strict henselization.
2. At an interior point, restrict to an open neighbourhood contained in the open curve.
   There the immersion is the identity, whose direct image is exact
   (`def-weil-open-immersion`, `def-weil-pbc-direct-image`), so every positive higher
   direct image, and hence its stalk, is zero.
3. At a boundary point P, the local ring is a Noetherian DVR by
   `lem-sc-smooth-connected-curve-local-rings`. By `lem-sc-strict-henselization-dvr`, its
   strict henselization is a DVR and the local ring map is flat local and injective.
   The closed point maps to P; the generic point maps to the curve's generic point.
   Consequently removing the boundary leaves exactly the spectrum of the fraction field K
   of this strict henselization. By `def-weil-pbc-strict-henselization-limit`, each element
   comes from an etale neighbourhood, so K is algebraic over the curve function field.
   `cor-sc-hilbert-90-field` makes H^1(K, G_m) zero. Apply
   `lem-sc-brauer-algebraic-function-field-zero` with L = E = K to make H^2(K, G_m) zero.
   The stalk formula in step 1 yields both asserted vanishings. -/
theorem isZero_gm_higherDirectImage_stalk_of_open_curve_boundary
    {k : Type u} [Field k] [IsAlgClosed k] {Cbar C : Scheme.{u}}
    (f : Cbar ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (S : Set Cbar) (hS : S.Finite) (hclosed : ∀ P ∈ S, IsClosed ({P} : Set Cbar))
    (j : C ⟶ Cbar) [IsOpenImmersion j] (hj : Set.range j.base = Sᶜ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (xbar : Spec (.of Ω) ⟶ Cbar)
    (q : ℕ) (hq : q = 1 ∨ q = 2) :
    IsZero (((Scheme.pointSmallEtale xbar).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Cbar.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj C.gmSheaf)))) := by
  sorry

end AlgebraicGeometry
