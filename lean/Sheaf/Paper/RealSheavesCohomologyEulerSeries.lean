/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.AdicLocalCharacteristicFactor
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.GlobalGeometricFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Cohomology and the Euler series

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-cohom,
d-real-cohom, order 2947 (blueprint: d-real-cohom).

Ordinary abelian-sheaf cohomology is `Etale.cohomology` applied to the sheaf in degree
zero, with `Etale.rightDerivedGlobalSections` computing RΓ. For a Weil sheaf use the
imported ordinary/compact coefficient cohomology on its forgotten object. The integral
constructions take the finite-level derived inverse limit, rationalization inverts the
uniformizer (equivalently l), and the common-stage construction extends coefficients.
The operators are `globalGeometricFrobeniusOnCohomology`. Constant Weil twists and the
normalization Qbar(n)=B_(q^(-n)) are the imported `constantTwist` and `tateLine`.
These conventions are reused, not redefined. The new datum is the Euler series of an
arbitrary constructible sheaf in the recorded common-stage Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
open scoped PowerSeries.WithPiTopology
namespace RealSheaves

/-- Forget the coefficient embedding from the chapter setup to the existing field datum.
All fields and the chosen algebraic closure are retained literally.
Source: blueprint d-real-setup as used in cohomology (blueprint: d-real-cohom). -/
def Setup.finiteFieldDatum (D : Setup.{u, v}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := D.p
  a := D.a
  q := D.q
  prime := D.p_prime
  exponent_pos := D.a_pos
  cardinality_eq := rfl
  k₀ := D.k₀
  card_base := Nat.card_eq_fintype_card.trans D.card_eq
  k := D.k

variable (D : Setup.{u, v}) (C₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]

/-- The inverse local characteristic factor after coefficient embedding and T↦T^(e_x).
A closed point with zero stalk contributes one. No lissity or reality is assumed.
Source: blueprint main-20261015, d-real-cohom, Euler-series display (blueprint: d-real-cohom). -/
def eulerFactor
    (F : WeilConjectures.sfCommonStageWeilSheaf D.finiteFieldDatum D.l D.l_ne_p
      C₀ D.Qbar)
    (x : {x : C₀.left // x ∈ closedPoints C₀.left}) : PowerSeries ℂ :=
  ((((WeilConjectures.sfLocalCharacteristicFactor D.finiteFieldDatum D.l D.l_ne_p
    D.Qbar C₀ F x).map D.iota).comp
      (Polynomial.X ^ D.closedPointDegree C₀.left x) : Polynomial ℂ) : PowerSeries ℂ)⁻¹

/-- The locally finite formal Euler product L_iota(C₀,F,T), on precisely the curves
of the chapter setup. The finite-type instances are extracted from that curve hypothesis.
Closed points and degrees are those of the setup, and the local polynomials are the
recorded constructible-stalk factors.
Source: blueprint main-20261015, d-real-cohom, displayed product
(blueprint: d-real-cohom). -/
def eulerSeries (hC : D.IsCurve C₀.left)
    (F : @WeilConjectures.sfCommonStageWeilSheaf D.finiteFieldDatum D.l _ D.l_ne_p
      C₀ hC.2.2.2.1 hC.2.2.2.2.1 D.Qbar _ _ _) : PowerSeries ℂ :=
  letI : LocallyOfFiniteType C₀.hom := hC.2.2.2.1
  letI : QuasiCompact C₀.hom := hC.2.2.2.2.1
  letI : IsSeparated C₀.hom := hC.2.1
  ∏' x : {x : C₀.left // x ∈ closedPoints C₀.left}, eulerFactor (D := D) (C₀ := C₀) F x

/-- The formal product is locally finite, converges coefficientwise, and belongs to
1+T ℂ[[T]]. Local finiteness includes the precise bounded-degree closed-point assertion.
This is well-definedness of the displayed definition, not analytic convergence in T.
Source: blueprint d-real-cohom, product and final paragraph (blueprint: d-real-cohom).
Proof: finite type over the finite base field gives finitely many closed points of
bounded residue degree, by the bounded-degree theorem in PointCount. Every degree is
positive. A finite-stage determinant det(1-T F_x) has constant term one; this remains
true under scalar extension and the coefficient embedding. Substituting T^(e_x) and
inverting gives a factor congruent to one modulo T^(e_x). Outside the finite set of
points of degree at most n it is one modulo T^(n+1). Hence every coefficient of the
finite partial products stabilizes. Apply the coefficientwise product topology's
locally finite product criterion to obtain HasProd. The stabilized constant coefficient
is the empty product one, which is precisely membership in 1+T ℂ[[T]]. The zero sheaf
has determinant one at every point and gives the product one. -/
theorem eulerSeries_spec (hC : D.IsCurve C₀.left)
    (F : WeilConjectures.sfCommonStageWeilSheaf D.finiteFieldDatum D.l D.l_ne_p
      C₀ D.Qbar) :
    (∀ n : ℕ, {x : {x : C₀.left // x ∈ closedPoints C₀.left} |
      D.closedPointDegree C₀.left x ≤ n}.Finite) ∧
    (∀ n : ℕ, {x : {x : C₀.left // x ∈ closedPoints C₀.left} |
      ¬ (PowerSeries.X : PowerSeries ℂ) ^ (n + 1) ∣
        eulerFactor (D := D) (C₀ := C₀) F x - 1}.Finite) ∧
    HasProd (eulerFactor D C₀ F) (eulerSeries (D := D) (C₀ := C₀) hC F) ∧
    PowerSeries.constantCoeff (eulerSeries (D := D) (C₀ := C₀) hC F) = 1 := by
  sorry

end RealSheaves
