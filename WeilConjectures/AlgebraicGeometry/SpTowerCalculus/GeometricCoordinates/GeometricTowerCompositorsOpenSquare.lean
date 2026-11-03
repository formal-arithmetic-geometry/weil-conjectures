/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerCompositorParts

/-! # Finite square for the open compositor
Source: Stacks 0F7J, Tags 0F7B--0F7K.
(blueprint: lem-sp-geometric-tower-compositors-open-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite evaluation of the open compositor alone. Both proper factors remain
uncomposed on both sides of this square.
Source: Stacks 0F7J, exact open localization
(blueprint: lem-sp-geometric-tower-compositors-open-square).

Proof: the section-pinned graph pull and push comparisons preserve the ordinary
adjunction units and counits. Apply left-adjoint uniqueness to the ordinary open
composition and use sequence_open_word to identify its model image. Descend this
square by exact localization. Paste the normalized evaluations of the two open
factors and the two proper factors, applying naturality to the proper whiskerings.
The realization counits in the source and target comparisons cancel; the finite
coordinates are precisely finiteTowerIntermediateCoordinates followed by the
finite open compositor and T.i_q. No proper compositor is evaluated in this step.
The argument works for identity opens, empty opens, and the zero input. -/
theorem open_collapse_finite
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (fixedLevel l E b q Z n).map (openCollapse l E b o q g T K) ≫
        (afterOpenEvaluation l E b o q z T n).hom.app K =
      (towerIntermediateEvaluation l E b o q T n).hom.app K ≫
        (finiteOpenCollapse l E z T n).hom.app
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
