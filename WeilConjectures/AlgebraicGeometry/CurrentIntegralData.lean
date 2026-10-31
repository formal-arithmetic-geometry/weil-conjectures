/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionComparisons
public import WeilConjectures.AlgebraicGeometry.NormalizedModelIntegralAdjunction

/-! # Data of the integral clause of the composition comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.proof.md, integral clause
(blueprint: def-sp-current-integral-comparison-data).

`IntegralEdge` is one normalized integral realization of a supplied tower adjunction and
`IntegralResult` packages three such edges with the two integral compositors and their
laws. Both are extracted unchanged from `WeilConjectures.AlgebraicGeometry.CurrentCompositionComparisons`,
which re-exports them, so that the item and its helper modules share them without an
import cycle. The categories are bounded constructible internal modules over the
pulled-back completed ring.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompositionComparisons
open IntegralDirectImageTower NormalizedIntegralAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integral realization of one of the three given tower adjunctions.
Every functor is the recorded support restriction or the actual model Rlim G red.
The left comparison is the proper/open scalar mate, and the right comparison
is the reduction/limit counit, fixing the normalization of both arrows.
Source: comparisons (3), integral realization
(blueprint: def-sp-current-integral-comparison-data). -/
structure IntegralEdge (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) (a : towerSupport l E s c hF ⊣ G) where
  limitX : Limit l E s X
  limitY : Limit l E s Y
  reductionX : ∀ M : Constructible l E X, spConstructibleTorTowers l E X (s.towers X)
    ((red l E s X).obj M.obj)
  reductionY : ∀ K : Constructible l E Y, spConstructibleTorTowers l E Y (s.towers Y)
    ((red l E s Y).obj K.obj)
  normalized : ∀ K : Constructible l E Y,
    IsSpNormalizedTower l E X (s.towers X)
      (G.obj ((reduction l E s Y reductionY).obj K)).obj
  closed : ∀ K : Constructible l E Y,
    constantModelBoundedConstructible (spIntegralCondensed l E) X
      ((model l E s limitX reductionY G).obj K)
  supportClosed : ∀ M : Constructible l E X,
    constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((shriek l E c).obj M.obj)
  geometry : ReductionGeometry l E s
  openIso : OpenReductionIsIso l E s geometry
  leftComparison : support l E c supportClosed ⋙ reduction l E s Y reductionY ≅
    reduction l E s X reductionX ⋙ towerSupport l E s c hF
  left_normalization : ∀ M : Constructible l E X,
    (leftComparison.hom.app M).hom = towerBaseChange l E s geometry openIso c M.obj
  rightComparison : right l E s limitX reductionY G closed ⋙ reduction l E s X reductionX ≅
    reduction l E s Y reductionY ⋙ G
  right_normalization : ∀ K : Constructible l E Y,
    (rightComparison.hom.app K).hom =
      (redLimitAdjunction l E s X limitX).counit.app
        (G.obj ((reduction l E s Y reductionY).obj K)).obj
  adjunction : support l E c supportClosed ⊣ right l E s limitX reductionY G closed
  unit_reduction : ∀ M : Constructible l E X,
    (reduction l E s X reductionX).map (adjunction.unit.app M) =
      a.unit.app ((reduction l E s X reductionX).obj M) ≫
        G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _
  counit_reduction : ∀ K : Constructible l E Y,
    (reduction l E s Y reductionY).map (adjunction.counit.app K) =
      leftComparison.hom.app _ ≫ (towerSupport l E s c hF).map
        (rightComparison.hom.app K) ≫ a.counit.app ((reduction l E s Y reductionY).obj K)

/-- Integral composition on Dbc, together with its two whole-tower reduction equations.
The isomorphisms are normalized by the actual reduction/total-limit comparisons,
so they realize the given tower compositors rather than unrelated isomorphisms.
Source: comparisons (3), both integral isomorphisms
(blueprint: def-sp-current-integral-comparison-data). -/
def IntegralResult (s : Presentation l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (hFf : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s cf).obj M.obj))
    (hFg : ∀ M : Towers l E s Y, spConstructibleTorTowers l E Z (s.towers Z)
      ((towerShriek l E s cg).obj M.obj))
    (hFh : ∀ M : Towers l E s X, spConstructibleTorTowers l E Z (s.towers Z)
      ((towerShriek l E s ch).obj M.obj))
    (Gf : Towers l E s Y ⥤ Towers l E s X)
    (Gg : Towers l E s Z ⥤ Towers l E s Y)
    (Gh : Towers l E s Z ⥤ Towers l E s X)
    (af : towerSupport l E s cf hFf ⊣ Gf)
    (ag : towerSupport l E s cg hFg ⊣ Gg)
    (ah : towerSupport l E s ch hFh ⊣ Gh)
    (alphaTower : towerSupport l E s cf hFf ⋙ towerSupport l E s cg hFg ≅
      towerSupport l E s ch hFh)
    (thetaTower : Gh ≅ Gg ⋙ Gf) : Prop :=
  ∃ If : IntegralEdge l E s cf hFf Gf af,
  ∃ Ig : IntegralEdge l E s cg hFg Gg ag,
  ∃ Ih : IntegralEdge l E s ch hFh Gh ah,
  ∃ alpha : support l E cf If.supportClosed ⋙ support l E cg Ig.supportClosed ≅
      support l E ch Ih.supportClosed,
  ∃ theta : right l E s Ih.limitX Ih.reductionY Gh Ih.closed ≅
      right l E s Ig.limitX Ig.reductionY Gg Ig.closed ⋙
        right l E s If.limitX If.reductionY Gf If.closed,
    SpCompositionIntegralLaws
      (support l E cf If.supportClosed) (support l E cg Ig.supportClosed)
      (support l E ch Ih.supportClosed)
      (right l E s If.limitX If.reductionY Gf If.closed)
      (right l E s Ig.limitX Ig.reductionY Gg Ig.closed)
      (right l E s Ih.limitX Ih.reductionY Gh Ih.closed)
      If.adjunction Ig.adjunction Ih.adjunction
      (reduction l E s X If.reductionX) (reduction l E s Y Ig.reductionX)
      (reduction l E s Z Ih.reductionY)
      (towerSupport l E s cf hFf) (towerSupport l E s cg hFg)
      (towerSupport l E s ch hFh) Gf Gg Gh
      If.leftComparison Ig.leftComparison Ih.leftComparison
      If.rightComparison Ig.rightComparison Ih.rightComparison
      alphaTower thetaTower alpha theta

end AlgebraicGeometry.ProEtale.CompositionComparisons
