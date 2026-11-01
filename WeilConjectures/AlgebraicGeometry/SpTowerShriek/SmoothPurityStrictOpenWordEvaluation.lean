/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearEvaluationAcyclicLift
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private def properProjection (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : D l E X) (M : D l E Y) :=
  ((adjunction l E b (o.geometry f)).homEquiv _ _)
    ((o.geometry f).tensorPullback.hom.app ((push l E b (o.geometry f)).obj N, M) ≫
      (tensor l E b X).map
        (Prod.mkHom ((adjunction l E b (o.geometry f)).counit.app N) (𝟙 _)))

end AlgebraicGeometry.ProEtale.SpTowerShriek
