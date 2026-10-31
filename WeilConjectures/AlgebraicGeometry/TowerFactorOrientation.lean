/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurityBaseChangeData
public import WeilConjectures.AlgebraicGeometry.VectorPurityNormalization

/-! # Orientation part of tower purity base change
(blueprint: lem-sp-tower-factor-orientation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- Canonical unit and Tate-line pullback comparisons and the tower orientation square.
Source: latest blueprint purity-bc-factors proof (1)
(blueprint: lem-sp-tower-factor-orientation).

Proof: construct the unit comparison by exact pullback of the strict coefficient
unit and the Tate comparison from the finite Kummer pullback maps and their quotient
compatibility. These are maps of equally shifted sheaf towers; strict tower Hom
extensionality and full faithfulness of the shifted single embedding verify their
WordComparison equations. Apply finite_orientation_base_change at each quotient
ell^(n+1), using the normalized finite orientations in P.finite_levels and
P'.finite_levels. The evaluation formula for the counit mate is the one in
SpTowerMate.Laws. Uniqueness of right adjoints, preserving their counits, identifies
any supplied adjunctions with the ones furnished by the mate-evaluation theorem;
uniqueness of the adjoint transpose then gives the same evaluation formula.
Conjugate the resulting equation by the two orientations. Its endpoints
are equally shifted rank-one sheaf towers, so tower_orientation_transport detects
its equality from the finite equations. Transport through the fixed realization
counits to obtain the displayed orientation square. No conservativity assertion
about arbitrary derived morphisms and no normalization of input towers is used. -/
theorem tower_factor_orientation
    (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (X Y X' Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsNoetherian X'.left] [IsNoetherian Y'.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [QuasiCompact f'.left] [HasCompactification f'.left]
    (c : Compactification f.left) (a : SpTowerMate.Data ell E b o q sq c)
    (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q a x))
    (w : SpChartAdmissibility.Twists ell E X.left)
    (w' : SpChartAdmissibility.Twists ell E X'.left)
    (P : TowerPurityAt ell E b o q c d w a.support_closed a.right
      a.adjunction a.levels)
    (P' : TowerPurityAt ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
      a.right' a.adjunction' a.levels')
    (gu : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n u'.left)
    (gv : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n v.left) :
    ∃ (s : (SpTowerShriek.pull ell E b (o.geometry v.left)).obj
        (SpTowerGamma.unit ell E Y.left) ≅ SpTowerGamma.unit ell E Y'.left)
      (t : (SpTowerShriek.pull ell E b (o.geometry u'.left)).obj
        (SpTowerGamma.orderedLine ell E b X.left w d) ≅
          SpTowerGamma.orderedLine ell E b X'.left w' d),
      (∀ n : ℕ, SpTowerP1.WordComparison ell E n
        (SpTowerP1.pullWord ell E n b (o.geometry v.left) (gv n)
          (SpTowerP1.unitWord ell E n Y.left (P.coefficientsY n)))
        (SpTowerP1.unitWord ell E n Y'.left (P'.coefficientsY n)) s.hom
        (((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) v.left).mapIso
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y.left) ≪≫
          Etale.leftDerivedUpperStarUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) v.left ≪≫
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y'.left).symm).hom)) ∧
      (∀ n : ℕ, SpTowerP1.WordComparison ell E n
        (SpTowerP1.pullWord ell E n b (o.geometry u'.left) (gu n)
          (SpTowerGamma.coefficientWord ell E b X.left w P.roots n
            (P.unitsX n) (P.coefficientsX n) (P.tensors n) d))
        (SpTowerGamma.coefficientWord ell E b X'.left w' P'.roots n
          (P'.unitsX n) (P'.coefficientsX n) (P'.tensors n) d) t.hom
        ((Etale.vectorIntegrationBaseCoefficientPullback (SpTowerP1.levelRing ell E n)
          (ell ^ (n + 1)) (SpTowerP1.levelAnnihilates ell E n)
          (PurityFiniteSetting.purityTwistTransport (SpTowerP1.levelRing ell E n)
            (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
            (SpTowerP1.levelAnnihilates ell E n)) u'.left (P.unitsX n) d).hom)) ∧
      (SpTowerShriek.pull ell E b (o.geometry u'.left)).map P.orientation.hom ≫
          towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s =
        t.hom ≫ P'.orientation.hom := by sorry

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
