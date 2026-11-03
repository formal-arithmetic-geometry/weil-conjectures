/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # The actual compact-support functor on the full tower subcategories

Source: current smooth-purity blueprint, `det-sp-tower-gluing`, Gluing.
(blueprint: def-sp-tower-restricted-support).
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

/-- Restrict the given compact-support functor using its proved preservation.
Source: latest smooth-purity blueprint, Gluing, representing functor
(blueprint: def-sp-tower-restricted-support).

Construction: compose the inclusion of the source full subcategory with the actual
compact-support functor, and apply ObjectProperty.lift with hF. Its object and map
are exactly the underlying compact-support object and map with the property proof.
This is the same explicit lift as the older support definition.
-/
def towerSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)) :
    SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q Y :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.F l E b o q c) hF

end AlgebraicGeometry.ProEtale.SpTowerGluing
