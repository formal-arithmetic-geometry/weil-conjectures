/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.Paper.PointHeartFiniteStageData

/-! # A step of the exact point-heart and finite-stage argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The finite-stage algebraic data, before applying the point-fibre functor.
Source: steps 8--9 of lem-zl-point-heart-finite-stage
(blueprint: lem-zl-point-weil-simultaneous-descent). -/
structure ZlPointFiniteStageDescentData
    (F : sfCommonStageWeilSheaf D l hl (zlPointHeartBase D) Ω)
    where
  A : Padic.FiniteCoefficientFields l Ω
  target_le : F.obj.carrier.stage ≤ A
  M : sfWeilSheaf D l hl (zlPointHeartBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
  targetTheta : (sfWeilFrobeniusPullback D l hl (zlPointHeartBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).obj
      (F.obj.carrier.toStage target_le) ≅ F.obj.carrier.toStage target_le
  u : M.obj.carrier ≅ F.obj.carrier.toStage target_le
  intertwining : M.obj.str.hom ≫ u.hom =
    (sfWeilFrobeniusPullback D l hl (zlPointHeartBase D)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).map u.hom ≫ targetTheta.hom
  target_structure :
    (sfCommonStageWeilFrobeniusPullback D l hl (zlPointHeartBase D) Ω).mapIso
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
          (D.geometricFiber (zlPointHeartBase D)).left).isoToStage F.obj.carrier target_le) ≪≫
      sfWeilStagePullbackIdentification D l hl (zlPointHeartBase D) Ω A
        (F.obj.carrier.toStage target_le) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion A).mapIso targetTheta ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
        (D.geometricFiber (zlPointHeartBase D)).left).isoToStage
          F.obj.carrier target_le).symm = F.obj.str
  e : sfWeilStageObject D l hl (zlPointHeartBase D) Ω A M.obj ≅ F.obj
  e_hom : e.hom.hom.f =
    (GeneralAlgebraicallyClosedCoefficients.inclusion A).map u.hom ≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
        (D.geometricFiber (zlPointHeartBase D)).left).isoToStage
          F.obj.carrier target_le).inv
  e_inv : e.inv.hom.f =
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
      (D.geometricFiber (zlPointHeartBase D)).left).isoToStage F.obj.carrier target_le).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion A).map u.inv

/-- A common-stage Weil sheaf has a heart model and all Weil isomorphism
identities at one common finite coefficient stage, retaining its raw target.
Source: BBD 1.3.3--1.3.4; paragraph 7 of the dimension-zero argument and steps
5, 8--9 of lem-zl-point-heart-finite-stage
(blueprint: lem-zl-point-weil-simultaneous-descent).

Proof: choose the finite-stage heart model tauGE(0) tauLE(0) of the raw carrier.
Its canonical maps give an isomorphism to that carrier in the common-stage heart.
Transport the given Frobenius and its inverse along this isomorphism. Pullback by
Frobenius preserves the heart and is computed at coefficient stages. Represent the
two carrier maps, two structure maps and their inverses at common finite stages.
Each inverse and intertwining identity in the Hom colimit holds at some further
finite extension. A compositum of the finitely many fields makes all identities
hold simultaneously. The heart model remains in the heart under this extension.
The carrier maps now give u; the transported structure gives the finite Weil sheaf
M; the representatives of the original structure give targetTheta. Applying the
stage inclusion and its canonical isoToStage gives e with the displayed formulas
for e.hom and e.inv and the equality with the original structure. This argument
uses only finite lists of morphisms and equations, including for the zero object;
it imposes no continuity condition on powers of Frobenius. -/
theorem zl_point_weil_simultaneous_descent
    (F : sfCommonStageWeilSheaf D l hl (zlPointHeartBase D) Ω) :
    Nonempty (ZlPointFiniteStageDescentData D l hl Ω F) := by sorry

end WeilConjectures
