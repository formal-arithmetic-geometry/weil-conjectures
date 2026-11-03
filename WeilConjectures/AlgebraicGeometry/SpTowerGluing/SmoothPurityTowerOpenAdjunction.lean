/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # The canonical open adjunction in ordinary tower coordinates

Source: current smooth-purity blueprint, `det-sp-tower-gluing`, Gluing.
(blueprint: def-sp-tower-open-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Compose the realization equivalences with the actual derived open adjunction.
Source: latest smooth-purity blueprint, Local pairs and Gluing, open restriction
(blueprint: def-sp-tower-open-adjunction).

Construction: transport the derived extension/pullback adjunction for o.openOp j
through the recorded realization equivalence at the source and target. Composition
of these three adjunctions gives the specified open-extension/pullback adjunction.
This is the same explicit composite as the older openAdjunction definition.
-/
def towerOpenAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    SpTowerCalculus.openExtension l E b o q j ⊣ SpTowerCalculus.etalePullback l E b o q j :=
  ((SpTowerCalculus.realization l E b U (q.abelian U)).toAdjunction.comp
    (o.openOp j).derivedAdjunction).comp
    (SpTowerCalculus.realization l E b T (q.abelian T)).symm.toAdjunction

end AlgebraicGeometry.ProEtale.SpTowerGluing
