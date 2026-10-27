/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.FiniteSmoothCoefficientArrows

/-! # Canonical comparisons for purity and tower reductions

These are the unchanged evaluation words and arrows formerly defined in
`PurityConjugatesTowerReduction`. Separating their definition permits the two
coefficient-transport steps to be stated without an import cycle.
Source: tower-geometric gamma proof (3)
(blueprint: def-sp-purity-reduction-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpPurityReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [b : SpTowerShriek.Base l E] (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The actual levelwise derived pullback, Tate twist, and even shift, transported
back to the original ordinary derived category of strict towers.
Source: gamma proof (3) (blueprint: def-sp-purity-reduction-comparisons). -/
def pullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
    ((SpTowerGamma.source l E b o q f w d).obj K)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q c hF G adj)
  (roots : SpCoordinateAdjunction.RootLines l E X)
  (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
  (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
  (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X)
  (gc : ∀ n : ℕ, SpTowerP1.GeometricCoordinates l E n f)

/-- The fixed pullback/tensor evaluation word of the purity source. It uses the
retained etale origin, root generators, and normalized K-flat tensor comparisons.
Source: gamma proof (3) (blueprint: def-sp-purity-reduction-comparisons). -/
def sourceWord (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  SpTowerP1.tensorWord l E n b (tc n)
    (SpTowerP1.pullWord l E n b (o.geometry f) (gc n)
      (SpTowerGamma.inputWord l E b o q c hF G adj lv n K))
    (SpTowerGamma.coefficientWord l E b X w roots n (unitsX n) (cc n) (tc n) d)

/-- The canonical source comparison in the original strict-tower evaluation.
It includes the realization counit and the prescribed evaluation comparison.
Source: gamma proof (3) (blueprint: def-sp-purity-reduction-comparisons). -/
def sourceComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  (sourceWord l E o q c w d hF G adj lv roots unitsX cc tc gc n K).comparison ≫
    (SpTowerShriek.Ev l E X n).map
      ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.inv.app
        ((SpTowerGamma.source l E b o q f w d).obj K)) ≫
    (SpTowerCalculus.levelComparison l E b q X n).hom.app
      (pullbackTower l E o q f w d K)

/-- The exceptional-output comparison, using the finite right adjoint's actual
counit-normalized realization and the glued evaluation comparison.
Source: gamma proof (3) (blueprint: def-sp-purity-reduction-comparisons). -/
def targetComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerGamma.targetWord l E b o q c hF G adj lv n K).comparison ≫
    (SpTowerCalculus.levelComparison l E b q X n).hom.app (G.obj K).obj

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
