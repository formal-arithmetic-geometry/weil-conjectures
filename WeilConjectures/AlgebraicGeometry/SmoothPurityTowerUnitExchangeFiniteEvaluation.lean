/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurityBaseChangeData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.TowerP1LevelWords
public import WeilConjectures.AlgebraicGeometry.TowerP1GeometricCoordinates
public import WeilConjectures.SecSmoothPurity.MixedBaseChangeOperations
public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-!
# Finite evaluation of the tower unit exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, proof (1)
(blueprint: lem-route-tower-unit-exchange-finite-evaluation).

The statement records the finite compact-support exchange, its unit mate evaluation,
and the ordinary-etale dualizing base-change arrow represented by the resulting word.
All data are the supplied tower mate and purity records; no `SpTowerMate.Laws` field
is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- The prescribed ordinary-etale identification of a retained unit output.
It is the inverse counit-preserving `finiteRightComparison`, followed by the
retained ordinary right adjoint applied to `ui.inv`. The output `rightIso` remains
in `targetWord.comparison`; no endpoint isomorphism is chosen.
Source: latest blueprint purity-bc-factors proof (1), finite unit identifications
(blueprint: lem-route-tower-unit-exchange-finite-evaluation). -/
def unitEtaleIdentification
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [HasCompactification f]
    (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C ell E b q X,
      spConstructibleTorTowers ell E Y (q.abelian Y)
        ((SpTowerCalculus.F ell E b o q c).obj M.obj))
    (G : SpTowerCalculus.C ell E b q Y ⥤ SpTowerCalculus.C ell E b q X)
    (adj : SpTowerGluing.support ell E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels ell E b o q c hF G adj)
    (n : ℕ) [Finite (SpTowerShriek.R ell E n)]
    (K : SpTowerCalculus.C ell E b q Y)
    (ui : (lv.realization n).origin.obj
      ((SpTowerGluing.level ell E b q Y n).obj K) ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing ell E n) Y) :
    Etale.dualizingComplex (SpTowerP1.levelRing ell E n) f ≅
      (SpTowerGamma.targetWord ell E b o q c hF G adj lv n K).etale := by
  rcases c with ⟨Z, p, j, rfl, hp, hj⟩
  exact (SpTowerGamma.finiteRightComparison (SpTowerShriek.R ell E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n)
    (lv.realization n)).symm.app _ ≪≫ (lv.realization n).right.mapIso ui.symm

/--
Finite exchange is invertible on every finite constructible input, its counit mate
evaluates at the coefficient unit as the finite mate followed by the evaluated unit
identification, and the resulting tower arrow is represented by the ordinary-etale
dualizing base-change map.

(blueprint: lem-route-tower-unit-exchange-finite-evaluation)

Source: latest blueprint purity-bc-factors proof (1), unit component of the mate.

Proof:
1. For each finite input K, use the origin and rightIso in the supplied reduction
realization to express G_n K as a site-realized bounded-below ordinary-etale object.
Finite compact-support base change and exchange transport identify its invertible
exchange with the actual finiteExchange for c and c.ofIsPullback sq. This gives
hfinite for every finite input, including inputs not lifted from towers.
2. Expand the proper part of beta as unit, square compositor, and counit. Geometric
adjunction evaluation sends its end factors to the finite unit and counit, and
Operations.comp_evaluation sends its middle factor to the finite pullback square.
3. Expand the inverse open comparison by its defining adjunction transpose. The
open unit evaluation and ordinary open counit equation evaluate its two end factors;
composition evaluation handles the middle factor. Evaluation preserves inverses,
so composing with step 2 evaluates the entire compactification exchange.
4. Substitute the normalization of the two supplied support evaluations. Naturality
of realization counits cancels the intervening realization/inverse-realization pairs.
The result is the exchange equation in the original finite coordinates, with precisely
the recorded support and pull evaluations, without a Laws hypothesis.
5. Expand the primed Hom equivalence as unit followed by the right adjoint. Substitute
the recorded primed unit equation. For the defining transpose of mate, use step 4 to
move the inverse exchange and the unprimed counit equation to cancel its remaining
right comparison. The finite Hom bijection gives mate evaluation through the exact
sourceComparison and targetComparison.
6. Set delta = towerUnitIdentification and delta_n = pullEvaluation.inv followed by
level.map delta. Naturality of the primed right comparison at delta turns step 5 at
the unit into the displayed full unit-exchange evaluation, with G'_n(delta_n).
The inverse realization and unitIso.inv on the left are precisely the realization
counits transporting towerUnitExchange to the original coordinates. Expand delta;
the realization triangle identity identifies delta_n with the component of s.
7. Take any ui and ui' satisfying the displayed FiniteLevels unit-word equations.
Their existence follows from P.finite_levels and P'.finite_levels. Finite site
comparison is fully faithful on the bounded-below origins and their exact pullbacks.
The first WordComparison for s and the two unit-word equations therefore identify
its ordinary arrow with pullback(ui), the ordinary unit map, and inverse(ui').
8. Substitute the counit-compatibility equation of each realization.rightIso into
the finite transpose from step 6. Exchange transport turns its inverse exchange
into the ordinary-etale exchange for c and c'. Full faithfulness reflects this
calculation, so it determines the map itself, not merely its endpoints.
9. The right-adjoint uniqueness defining finiteRightComparison preserves counits.
Use those two equations and counit naturality at ui to replace the retained right
adjoints by canonical upper shriek. Naturality of the exchange moves ui through
its inverse; ui' cancels its inverse from step 7. The remaining transpose is the
inverse ordinary compact-support exchange, pulled-back counit, and ordinary unit
map. This is exactly dualizingComplexBaseChangeMap. The displayed identification
uses only finiteRightComparison and right.mapIso(ui.symm); targetWord supplies
rightIso and the level comparison, and pullWord gu supplies the source pullback.
10. Compactification independence of the finite exchange and counit-preserving
uniqueness of right adjoints identify this computation with the canonical one.
All exchanges use the supplied sq. The proof also applies to n = 0, d = 0, zero
objects, empty schemes, and the identity square, without faithfulness of tower
evaluation or replacing the supplied a.
-/
theorem tower_unit_exchange_finite_evaluation
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
    (gv : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n v.left)
    (s : (SpTowerShriek.pull ell E b (o.geometry v.left)).obj
        (SpTowerGamma.unit ell E Y.left) ≅ SpTowerGamma.unit ell E Y'.left)
    (hs : ∀ n : ℕ, SpTowerP1.WordComparison ell E n
      (SpTowerP1.pullWord ell E n b (o.geometry v.left) (gv n)
        (SpTowerP1.unitWord ell E n Y.left (P.coefficientsY n)))
      (SpTowerP1.unitWord ell E n Y'.left (P'.coefficientsY n)) s.hom
      (((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) v.left).mapIso
        (Etale.singleFunctorObjUnitIso
          (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y.left) ≪≫
        Etale.leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) v.left ≪≫
        (Etale.singleFunctorObjUnitIso
          (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y'.left).symm).hom)) :
    ∃ hfinite : ∀ n : ℕ, letI : Finite (SpTowerShriek.R ell E n) := b.finite n
      ∀ K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R ell E n),
        IsIso ((SpTowerMate.finiteExchange ell E b (sq := sq) (c := c) n).app
          ((a.levels.right n).obj K).obj),
      (∀ n : ℕ, letI : Finite (SpTowerShriek.R ell E n) := b.finite n
        let K₀ : SpTowerCalculus.C ell E b q Y.left :=
          ⟨SpTowerGamma.originalUnit ell E b q Y.left, P.unit_mem⟩
        let K₀' : SpTowerCalculus.C ell E b q Y'.left :=
          ⟨SpTowerGamma.originalUnit ell E b q Y'.left, P'.unit_mem⟩
        (spDerivedCoefficientEvaluation ell E X'.left (q.abelian X'.left) n).map
            ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.map
                (towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s) ≫
              (SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).unitIso.inv.app
                (a.right'.obj K₀').obj) ≫
          ((a.levels'.comparison n).hom.app K₀').hom =
        (SpTowerMate.sourceComparison ell E b o q a n K₀).hom ≫
          (SpTowerMate.finiteMate ell E b o q a n
            ((SpTowerGluing.level ell E b q Y.left n).obj K₀)
            (hfinite n ((SpTowerGluing.level ell E b q Y.left n).obj K₀))).hom ≫
          ((a.levels'.right n).map (ObjectProperty.homMk
            ((SpTowerMate.pullEvaluation ell E b o q v.left n).inv.app K₀.obj ≫
              (spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).map
                (towerUnitIdentification ell E b o q a P.unit_mem P'.unit_mem s).hom))).hom) ∧
      (∀ n : ℕ, letI : Finite (SpTowerShriek.R ell E n) := b.finite n
        let K₀ : SpTowerCalculus.C ell E b q Y.left :=
          ⟨SpTowerGamma.originalUnit ell E b q Y.left, P.unit_mem⟩
        let K₀' : SpTowerCalculus.C ell E b q Y'.left :=
          ⟨SpTowerGamma.originalUnit ell E b q Y'.left, P'.unit_mem⟩
        ∀ (ui : (a.levels.realization n).origin.obj
              ((SpTowerGluing.level ell E b q Y.left n).obj K₀) ≅
                Etale.ordinaryFiniteUnit (SpTowerP1.levelRing ell E n) Y.left)
          (ui' : (a.levels'.realization n).origin.obj
              ((SpTowerGluing.level ell E b q Y'.left n).obj K₀') ≅
                Etale.ordinaryFiniteUnit (SpTowerP1.levelRing ell E n) Y'.left),
          (SpTowerP1.nu ell E n Y.left).map ui.hom ≫
              (SpTowerP1.unitWord ell E n Y.left (P.coefficientsY n)).comparison =
            (SpTowerGamma.inputWord ell E b o q c a.support_closed a.right
              a.adjunction a.levels n K₀).comparison ≫
              (SpTowerShriek.Ev ell E Y.left n).map
                ((SpTowerCalculus.realization ell E b Y.left (q.abelian Y.left)).counitIso.hom.app
                  (SpTowerGamma.unit ell E Y.left)) →
          (SpTowerP1.nu ell E n Y'.left).map ui'.hom ≫
              (SpTowerP1.unitWord ell E n Y'.left (P'.coefficientsY n)).comparison =
            (SpTowerGamma.inputWord ell E b o q (c.ofIsPullback sq) a.support_closed'
              a.right' a.adjunction' a.levels' n K₀').comparison ≫
              (SpTowerShriek.Ev ell E Y'.left n).map
                ((SpTowerCalculus.realization ell E b Y'.left
                  (q.abelian Y'.left)).counitIso.hom.app (SpTowerGamma.unit ell E Y'.left)) →
          SpTowerP1.WordComparison ell E n
            (SpTowerP1.pullWord ell E n b (o.geometry u'.left) (gu n)
              (SpTowerGamma.targetWord ell E b o q c a.support_closed a.right
                a.adjunction a.levels n K₀))
            (SpTowerGamma.targetWord ell E b o q (c.ofIsPullback sq)
              a.support_closed' a.right' a.adjunction' a.levels' n K₀')
            (towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s)
            (((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) u'.left).mapIso
                (unitEtaleIdentification ell E b o q c a.support_closed a.right
                  a.adjunction a.levels n K₀ ui)).inv ≫
              Etale.dualizingComplexBaseChangeMap (SpTowerP1.levelRing ell E n) sq ≫
              (unitEtaleIdentification ell E b o q (c.ofIsPullback sq) a.support_closed'
                a.right' a.adjunction' a.levels' n K₀' ui').hom)) := by
  sorry

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
