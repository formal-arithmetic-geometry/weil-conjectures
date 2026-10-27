/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-! # A single semilinear Frobenius step on point fibres

Source: the local Frobenius conjugacy proof, steps 2--6
(blueprint: lem-weil-local-frobenius-step-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (K : sfWeilComplex D c.l c.different Y₀ E.val)
  (x x' : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
  (hs : x ≫ (D.geometricFrobenius Y₀).hom = (frobeniusPointIso D).hom ≫ x')

/-- The specified one-step transport, followed by the pulled-back Weil structure.
Its direction is from the next point fibre to the preceding point fibre.
Source: local Frobenius conjugacy, the map A_i of proof step 4
(blueprint: lem-weil-local-frobenius-step-compatibility). -/
def localFrobeniusStepTransport :
    localPointComplex c.l E.val D c.different Y₀ K x' ⟶
      localPointComplex c.l E.val D c.different Y₀ K x :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Y₀
  localPointTransport c.l E.val D c.different
      (localDerivedStalk c.l E.val D c.different Y₀ K x') ≫
    (pointRationalFibre D c.l c.different E.val).map
      ((localPullbackComposition c.l E.val (frobeniusPointIso D).hom x' K.carrier).inv ≫
        eqToHom (congrArg
          (fun f ↦ (rationalDerivedPullback c.l E.val f).obj K.carrier) hs.symm) ≫
        (localPullbackComposition c.l E.val x
          (D.geometricFrobenius Y₀).hom K.carrier).hom ≫
        (rationalDerivedPullback c.l E.val x).map K.str.hom)

private theorem localPointTransport_isIso
    (N : sfRationalConstructibleCategory c.l E.val (Spec (.of D.k))) :
    IsIso (localPointTransport c.l E.val D c.different N) := by
  let S₀ : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)
  have : IsProper S₀.hom := by dsimp [S₀]; infer_instance
  have : LocallyOfFiniteType S₀.hom := by dsimp [S₀]; infer_instance
  have : QuasiCompact S₀.hom := by dsimp [S₀]; infer_instance
  have : IsSeparated S₀.hom := by dsimp [S₀]; infer_instance
  let C₀ : Compactification S₀.hom := Compactification.ofIsProper _
  have h := (frobeniusCohomologyTransport_isIso D c.l c.different S₀ c.Qbar C₀
    (0 : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar
      (D.geometricFiber S₀).left)).2.2.2
  have : IsIso (frobeniusPointTransportRational D c.l c.different E.val N) :=
    (h E.val C₀ N 0).1
  unfold localPointTransport
  infer_instance

/-- The one-step map is invertible: point transport is invertible, and every remaining
factor is a composition comparison or the image of the Weil isomorphism.
Source: point-transport invertibility and local Frobenius conjugacy step 4
(blueprint: lem-weil-local-frobenius-step-compatibility). -/
instance localFrobeniusStepTransport_isIso :
    IsIso (localFrobeniusStepTransport D c E Y₀ K x x' hs) := by
  have := localPointTransport_isIso D c E
    (localDerivedStalk c.l E.val D c.different Y₀ K x')
  unfold localFrobeniusStepTransport
  infer_instance

/-- A single specified semilinear step intertwines equal-length local return operators.
Here n denotes the positive exponent n+1, as in localFrobeniusOperator. This is a
local calculation for two consecutive points; no closed point, residue embedding,
or enumeration of a finite orbit is assumed.

Source: current blueprint, sec-poincare-duality/sk-thm-frobenius,
lem-weil-local-frobenius-conjugacy-class.proof.md, the sentence about intertwining
at one translate; expanded DAG proof steps 2--6
(blueprint: lem-weil-local-frobenius-step-compatibility).

Proof: write J_i for pullback to the successive reparametrized points followed by
point fibre, tau_i for point transport and composition comparison, and A_i for
J_i(theta) tau_i. Expand the n+1-fold transport using its defining recursion.
Naturality of point transport moves each pulled-back theta past the next tau;
associativity of the localized integral pullback comparisons identifies the two
parenthesizations. Induction gives the product A_i ... A_(i+n). The return equations
identify the last point with the first via the same h_s^(n+1) reparametrization.
Expanding at the next point gives the cyclically shifted product. Composing either
product with A_i yields the same ordered product of n+2 factors, by associativity.
The equalities of scheme morphisms used in the comparison agree by proof
irrelevance. This proves the displayed equality for the actual specified maps.
For n=0 this is the naturality square with theta itself; the argument also applies
to zero complexes and requires no separatedness of Y₀. -/
theorem localFrobeniusStepCompatibility (n : ℕ)
    (hx : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x)
    (hx' : x' ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x') :
    localFrobeniusStepTransport D c E Y₀ K x x' hs ≫
        localFrobeniusOperator c.l E.val D c.different Y₀ K x n hx =
      localFrobeniusOperator c.l E.val D c.different Y₀ K x' n hx' ≫
        localFrobeniusStepTransport D c E Y₀ K x x' hs := by sorry

end WeilConjectures
