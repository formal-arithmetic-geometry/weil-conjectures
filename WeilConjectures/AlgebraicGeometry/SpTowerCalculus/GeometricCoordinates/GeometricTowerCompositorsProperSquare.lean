/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerCompositorParts

/-! # Finite square for the proper compositor
Source: Stacks 0F7J, Tags 0F7B--0F7K.
(blueprint: lem-sp-geometric-tower-compositors-proper-square).
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

/-- Finite evaluation of the proper compositor alone. The single open factor
is held fixed, so this square starts at the three-factor word afterOpen.
Source: Stacks 0F7J, right-derived proper composition
(blueprint: lem-sp-geometric-tower-compositors-proper-square).

Proof: the section pins identify the ordinary direct-image composition square
with the canonical pushforward composition. Right derivation transports this
square using K-injective representatives; rightDerivedLowerStarComp identifies
the resulting comparison with the canonical finite proper compositor. Paste the
evaluation of the already-composed open factor and the two proper factors.
Naturality and the realization triangle identities cancel the adjacent units
and counits. Use ve.normalization to replace the target support evaluation by
fixedEvaluation. The remaining finite word is finiteProperCollapse with T.p_g.
No composition of open extensions is evaluated here. Identity proper maps and
zero inputs are covered by the same adjunction identities. -/
theorem proper_collapse_finite
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ)
    (ve : Evaluation l E b o q T.cfg n)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (fixedLevel l E b q Z n).map (properCollapse l E b o q g T K) ≫
        (fixedEvaluation l E b o q z T.cfg n ve).hom.app K =
      (afterOpenEvaluation l E b o q z T n).hom.app K ≫
        (finiteProperCollapse l E T n).hom.app
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
