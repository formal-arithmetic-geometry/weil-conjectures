/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups G7 and J3
-/
module

public import Sheaf.Paper.IntegralReconstructionComparisonData
public import Sheaf.Paper.SmoothPurityBaseChangeFactors

/-! # Realization of the whole-tower base-change equations

This separates the existing functorial realization proof for compilation.
Source: purity-transport Steps 1--2 and base-change-factors.
(blueprint: lem-pur-integral-base-change-realization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem map_twice_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) {M N : A} {a b : M ⟶ N} (h : a = b) :
    G.map (F.map a) = G.map (F.map b) := congrArg (fun t ↦ G.map (F.map t)) h

private theorem map_exists_two
    {S T : Sort*} {P : S → Prop} {Q : T → Prop} {R R' U U' : S → T → Prop}
    (h : ∃ s t, P s ∧ Q t ∧ R s t ∧ U s t)
    (hR : ∀ s t, R s t → R' s t) (hU : ∀ s t, U s t → U' s t) :
    ∃ s t, P s ∧ Q t ∧ R' s t ∧ U' s t := by
  obtain ⟨s, t, hp, hq, hr, hu⟩ := h
  exact ⟨s, t, hp, hq, hR s t hr, hU s t hu⟩


namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence
attribute [local irreducible] SpTowerCalculus.realization SpIntegralAdjunction.limit
  SmoothPurityBaseChange.towerUnitExchange SmoothPurityBaseChange.towerExchange
  SmoothPurityBaseChange.towerTensorComparison SmoothPurityBaseChange.towerGamma
open SmoothPurityBaseChange

section BaseChange
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- Cartesian base change for the actual integral total-limit orientation and
purity components. The exchange is the prescribed counit mate, and the unit and
Tate comparisons retain their finite Kummer normalizations. Conjugating this equation
by the reconstruction units is the gammaH equation; the fixed-counit comparisons
give the gammaT equation.
Source: purity-transport Steps 1--2 and base-change-factors, tower consequence.
(blueprint: lem-pur-integral-base-change-realization).

Proof: base-change-factors identifies the actual strict-tower orientation and gamma
words, with the compact-support exchange and its counit mate. Apply the coordinate
inverse and total derived limit to those two equalities. Reconstruction-adjunction
calculus identifies the resulting pullback and exceptional comparisons, including
their counit normalizations; the unit/counit triangles cancel the intermediate
reconstruction comparisons. Thus the whole-system equation is the equation for the
realized maps, not an inference from separate finite-level equality. Conjugate by the
counit-preserving exceptional comparisons to obtain the same equation for gammaT. -/
theorem baseChange_realization
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
    (RX : SpReductionTower ell E X'.left (q.abelian X'.left))
    (NX : SpNormalizedEquivalence ell E X'.left (q.abelian X'.left) RX) :
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
      (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX).map
        ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.map
          ((SpTowerShriek.pull ell E b (o.geometry u'.left)).map P.orientation.hom ≫
          towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s)) =
      (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX).map
        ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.map
          (t.hom ≫ P'.orientation.hom)) ∧
      ∀ K : SpTowerCalculus.C ell E b q Y.left,
        (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX).map
          ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.map
            ((SpTowerShriek.pull ell E b (o.geometry u'.left)).map
            (towerGamma ell E b o q c d w a.support_closed a.right
              a.adjunction a.levels P K) ≫ towerExchange ell E b o q a x hb K)) =
        (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX).map
          ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.map
            ((towerTensorComparison ell E b o q a K _).hom ≫
            (SpTowerShriek.tensor ell E b X'.left).map (Prod.mkHom (𝟙 _) t.hom) ≫
            towerGamma ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
              a.right' a.adjunction' a.levels' P'
                ((SpTowerMate.V ell E b o q a).obj K))) := by
  refine map_exists_two
    (SmoothPurityBaseChange.tower_factors ell E b o q
      D _hne X Y X' Y' f v u' f' sq d c a x hb w w' P P' gu gv) ?_ ?_
  · intro s t ho
    exact map_twice_eq
      (SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse
      (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX) ho
  · intro s t hg K
    exact map_twice_eq
      (SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse
      (SpIntegralAdjunction.limit ell E X'.left (q.abelian X'.left) RX NX) (hg K).2

end BaseChange
end AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence
