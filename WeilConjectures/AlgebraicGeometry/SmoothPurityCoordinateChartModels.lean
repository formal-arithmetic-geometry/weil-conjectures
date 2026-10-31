/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoordinateProjectionModels
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoordinateComposition
public import WeilConjectures.AlgebraicGeometry.SmoothPurityEtaleNormalization

/-! # Explicit chart adjunction and finite compatibility

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-coordinate-chart-models).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Compose the specified étale pair with a projection pair before changing to
chart coordinates. This is an actual restricted adjunction, with both triangles.
Source: Local pairs, étale composition (blueprint: lem-sp-coordinate-chart-models). -/
def coordinateChartPair (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E k)
    (a : Foundations l E k b o q w)
    (p : ProjectionModels l E k b o q z h cal w a)
    (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (ch : Compactification (e ≫ proj Y.val.left d)) :
    ChartPair l E b o q e (proj Y.val.left d) ch (w U.val.left) d := by
  letI : e.IsOver (Spec (.of k)) := ⟨hOver⟩
  letI := hasCompactification_of_finiteType_over_field k U.val.left
    (space Y.val.left d) e
  let ce := HasCompactification.compactification e
  letI := hasCompactification_of_finiteType_over_field k
    (space Y.val.left d) Y.val.left (proj Y.val.left d)
  let cp := HasCompactification.compactification (proj Y.val.left d)
  exact restrictedComposite
    (etalePair l E k b o q z h cal U (coordinateBase Y d) e) (p.projection Y d cp)
    (fun M ↦ h (e ≫ proj Y.val.left d) ch M.obj M.property)
    (a.chart_closed Y U d e hOver)
    (Functor.isoWhiskerRight (cal.etale.etale_shriek e ce).symm
        (SpTowerCalculus.F l E b o q cp) ≪≫
      cal.composition.composition e (proj Y.val.left d) (e ≫ proj Y.val.left d)
        rfl ce cp ch)
    (composeRight l E b q _ _ _ (a.pulled Y U d e d).comparison)

/-- For the fixed intermediate compactifications, the explicit chart counit is
étale fibre summation followed by projection integration. Source: Local pairs;
Mathlib transported composite counit (blueprint: lem-sp-coordinate-chart-models). -/
theorem coordinateChartPair_counit
    (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E k)
    (a : Foundations l E k b o q w)
    (p : ProjectionModels l E k b o q z h cal w a)
    (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    (ch : Compactification (e ≫ proj Y.val.left d))
    (K : (P l E b q Y.val.left).FullSubcategory) :
    letI := hasCompactification_of_finiteType_over_field k U.val.left
      (space Y.val.left d) e
    let ce := HasCompactification.compactification e
    letI := hasCompactification_of_finiteType_over_field k
      (space Y.val.left d) Y.val.left (proj Y.val.left d)
    let cp := HasCompactification.compactification (proj Y.val.left d)
    (coordinateChartPair l E k b o q z h cal w a p Y U d e hOver ch).counit K =
      (SpTowerCalculus.F l E b o q ch).map
        ((composeRight l E b q _ _ _ (a.pulled Y U d e d).comparison).inv.app K.obj) ≫
      (cal.composition.composition e (proj Y.val.left d)
        (e ≫ proj Y.val.left d) rfl ce cp ch).inv.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (p.projection Y d cp).right_closed K⟩⟩ ≫
      (SpTowerCalculus.F l E b o q cp).map
        ((cal.etale.etale_shriek e ce).hom.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (p.projection Y d cp).right_closed K⟩⟩ ≫
          (etalePair l E k b o q z h cal U (coordinateBase Y d) e).counit
            ⟨_, (p.projection Y d cp).right_closed K⟩) ≫
      (p.projection Y d cp).counit K := by
  let := hasCompactification_of_finiteType_over_field k U.val.left
    (space Y.val.left d) e
  let ce := HasCompactification.compactification e
  let := hasCompactification_of_finiteType_over_field k
    (space Y.val.left d) Y.val.left (proj Y.val.left d)
  let cp := HasCompactification.compactification (proj Y.val.left d)
  simpa only [coordinateChartPair, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Iso.symm_inv, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, ce, cp] using
    restrictedComposite_counit
      (etalePair l E k b o q z h cal U (coordinateBase Y d) e) (p.projection Y d cp)
      (fun M ↦ h (e ≫ proj Y.val.left d) ch M.obj M.property)
      (a.chart_closed Y U d e hOver)
      (Functor.isoWhiskerRight (cal.etale.etale_shriek e ce).symm
          (SpTowerCalculus.F l E b o q cp) ≪≫
        cal.composition.composition e (proj Y.val.left d) (e ≫ proj Y.val.left d)
          rfl ce cp ch)
      (composeRight l E b q _ _ _ (a.pulled Y U d e d).comparison) K

/-- Evaluation and compactification independence of the explicitly composed chart
pairs, on all finite objects. Source: Local pairs and Levels.
(blueprint: lem-sp-coordinate-chart-models). -/
structure ChartModels (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E k)
    (a : Foundations l E k b o q w)
    (p : ProjectionModels l E k b o q z h cal w a) where
  chart_levels : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (coordinateChartPair l E k b o q z h cal w a p Y U d e hOver c) n
      (SpTowerShriek.finiteF l E b c n)
      (finiteChartRight l E b e (proj Y.val.left d) (w U.val.left) d n)
  _chart_left_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    (chart_levels Y U d e hOver c n).left = supportEvaluation l E b o q c n
  _chart_right_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (chart_levels Y U d e hOver c n).right.hom.app K =
      rightEvaluation l E b o q e (proj Y.val.left d) (w U.val.left) d n K
  chart_counit : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    (ce : Compactification e) (cp : Compactification (proj Y.val.left d))
    (ch : Compactification (e ≫ proj Y.val.left d))
    (K : (P l E b q Y.val.left).FullSubcategory),
    (coordinateChartPair l E k b o q z h cal w a p Y U d e hOver ch).counit K =
      (SpTowerCalculus.F l E b o q ch).map
        ((composeRight l E b q _ _ _ (a.pulled Y U d e d).comparison).inv.app K.obj) ≫
      (cal.composition.composition e (proj Y.val.left d)
        (e ≫ proj Y.val.left d) rfl ce cp ch).inv.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (p.projection Y d cp).right_closed K⟩⟩ ≫
      (SpTowerCalculus.F l E b o q cp).map
        ((cal.etale.etale_shriek e ce).hom.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (p.projection Y d cp).right_closed K⟩⟩ ≫
          (etalePair l E k b o q z h cal U (coordinateBase Y d) e).counit
            ⟨_, (p.projection Y d cp).right_closed K⟩) ≫
      (p.projection Y d cp).counit K

/-- Étale chart composition and its normalized finite adjunctions.
Source: latest blueprint Local pairs (étale composition) and Levels;
original coordinate argument steps 6--7.
(blueprint: lem-sp-coordinate-chart-models).

Proof. The definition coordinateChartPair composes the canonical étale sum-extension
adjunction with the ordered projection adjunction p.projection. The right composite is identified
with the displayed chart functor by a.pulled.comparison and composeRight; the
left composite is identified with the chosen chart compact support by the
calculus composition and étale-shriek comparisons. Restrict to the uniform full
subcategories using admissibility and preservation. Adjunction.comp supplies the
unit and both triangles. Its counit is projection integration after compact
support applied to the étale fibre sum. Transporting this counit through the two
specified comparisons gives exactly chart_counit; composition and refinement
coherence, together with href, gives this formula for every intermediate
compactification. The hcal hypothesis pins the actual graph comparison;
its varying-ring evaluation is the separate graph-summand theorem. At each
finite level compose the finite étale pair and the projection pair on all finite
constructible finite-Tor objects. Evaluate the actual tower Hom maps through
supportEvaluation and rightEvaluation. Their compatibility with the constituent
étale and projection transposes proves both transpose equations; evaluating the
identity transposes proves the unit and counit equations. The left comparison is
literally supportEvaluation and the right comparison is rightEvaluation. This
uses no claim that derived evaluations detect equality of arbitrary arrows. -/
theorem coordinate_chart_models
    (pchar : ℕ) [Fact pchar.Prime] (k : Type u) [Field k] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (hcal : SpTowerGluing.EtaleNormalized l E b o q k z cal.etale)
    (href : SpTowerGluing.EtaleRefinementCompatible l E b o q k z h cal)
    (w : TwistFamily l E k)
    (a : Foundations l E k b o q w)
    (p : ProjectionModels l E k b o q z h cal w a) :
    Nonempty (ChartModels l E k b o q z h cal w a p) := by sorry

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
