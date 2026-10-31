/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Gluing the local tower adjunctions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.md` (blueprint: det-sp-tower-gluing).

All levels n mean the positive exponent n+1. The categories are the recorded full
unnormalized uniformly constructible finite-Tor subcategories of ordinary derived towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Exact evaluation restricted to the recorded full finite-level category.
Source: clause (3), finite levels (blueprint: det-sp-tower-gluing). -/
def level (T : Scheme.{u}) (n : ℕ) :
    SpTowerCalculus.C l E b q T ⥤ spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n) :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q T ⋙
      spDerivedCoefficientEvaluation l E T (q.abelian T) n)
    (fun K ↦ K.property.1 n)

/-- The genuine full-subcategory restriction of the specified compactification functor.
Source: the representing functor (blueprint: det-sp-tower-gluing). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)) :
    SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q Y :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.F l E b o q c) hF

/-- The finite coefficient comparison is its specified counit transpose, not an arbitrary
map between exceptional inverse images. This is c_(n,m) of det-sp-reduction-exceptional.
Source: clause (3), reduction comparison (blueprint: det-sp-tower-gluing). -/
def coefficientMate {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (m n : ℕ) (h : m ≤ n)
    (hFn : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
        ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj))
    (hFm : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E m),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
        ((reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor X (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj))
    (Gn : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
      spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
    (Gm : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E m) ⥤
      spFiniteConstructibleTorCategory X (SpTowerShriek.R l E m))
    (an : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g hFn ⊣ Gn)
    (am : reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFm ⊣ Gm)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n))
    (hb : IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      (Gn.obj K).obj)) :
    (reductionCtfScalar (SpTowerCalculus.quotient l E h) X hSX).obj (Gn.obj K) ⟶
      Gm.obj ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y hSY).obj K) :=
  am.homEquiv _ _ (ObjectProperty.homMk
    (@inv _ _ _ _
      ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
        (Gn.obj K).obj) hb ≫
      (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
        (an.counit.app K).hom))

set_option maxHeartbeats 800000 in
-- Elaborating the dependent counit-mate reduction equation unfolds several derived functors.
/-- Finite adjunctions and their natural comparison to the tower right adjoint, with both
adjunction normalizations and the actual coefficient-mate reduction equation.
Source: clause (3), all finite levels and reductions (blueprint: det-sp-tower-gluing). -/
structure Levels {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : support l E b o q c hF ⊣ G) where
  finite_closed : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
      ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj)
  right : ∀ n : ℕ, spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
    spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)
  adjunction : ∀ n : ℕ,
    reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (finite_closed n) ⊣ right n
  realization : ∀ n : ℕ,
    ReductionExceptionalRealization (SpTowerShriek.R l E n) c.i c.g
      (finite_closed n) (right n) (adjunction n)
  support_evaluation : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q c n
  comparison : ∀ n : ℕ, G ⋙ level l E b q X n ≅ level l E b q Y n ⋙ right n
  counit : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Y),
    (support_evaluation n).comparison.inv.app (G.obj K).obj ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map (adj.counit.app K).hom =
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((comparison n).hom.app K).hom ≫
      ((adjunction n).counit.app ((level l E b q Y n).obj K)).hom
  unit : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X),
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map (adj.unit.app M).hom ≫
        ((comparison n).hom.app ((support l E b o q c hF).obj M)).hom ≫
        ((right n).map (ObjectProperty.homMk
          ((support_evaluation n).comparison.hom.app M.obj))).hom =
      ((adjunction n).unit.app ((level l E b q X n).obj M)).hom
  scalarX : ∀ (m n : ℕ) (h : m ≤ n)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor X (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj)
  scalarY : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj)
  direct_image_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      ((right n).obj K).obj)
  coefficient_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso (coefficientMate l E b c m n h (finite_closed n) (finite_closed m)
      (scalarX m n h) (scalarY m n h) (right n) (right m) (adjunction n) (adjunction m)
      K (direct_image_iso m n h K))
  reduction : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
        ((comparison n).hom.app K).hom ≫
      (coefficientMate l E b c m n h (finite_closed n) (finite_closed m)
        (scalarX m n h) (scalarY m n h) (right n) (right m) (adjunction n) (adjunction m)
        ((level l E b q Y n).obj K)
        (direct_image_iso m n h ((level l E b q Y n).obj K))).hom ≫
      ((right m).map (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))).hom =
    SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj ≫
      ((comparison m).hom.app K).hom

/-- The canonical open restriction counit in the strict tower coordinates.
Source: clause (1), restriction of representing pairs (blueprint: det-sp-tower-gluing). -/
def openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    SpTowerCalculus.openExtension l E b o q j ⊣ SpTowerCalculus.etalePullback l E b o q j :=
  ((SpTowerCalculus.realization l E b U (q.abelian U)).toAdjunction.comp
    (o.openOp j).derivedAdjunction).comp
    (SpTowerCalculus.realization l E b T (q.abelian T)).symm.toAdjunction

open SpCoordinateAdjunction in
end AlgebraicGeometry.ProEtale.SpTowerGluing

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
