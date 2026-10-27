/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.Paper.TowerScalarSingleCounit

/-! # Normalized scalar counit on the coefficient module
Source: blueprint classes proof (2), scalar coefficient normalization.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The normalized ordinary scalar counit on the coefficient module.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension; Stacks 06YY and 07A6.
(blueprint: lem-sp-tower-scalar-counit-normalization).

Proof: the coefficient module in degree zero is K-flat by the cochain tensor right
unitor. Apply the representative transpose formula of `ScalarData` to the induced
chain map from the ordinary coefficient arrow `e`. The adjunction on single
complexes has the ordinary adjunct as its degree-zero component. The exact
restriction single comparison identifies this derived transpose with the single of
`scalarGenerator`. The third Chern normalization gives the same transpose for
`scalarUnit`. Cancel the single comparison and use injectivity of the derived Hom
equivalence. This proves the displayed ordinary counit equation. -/
theorem scalarCounitNormalization {T : Scheme.{u}} (c : Chern l E T)
    (nc : c.Normalized l E)
    (e : c.scalar.model.E.obj (coefficient T (Rrings l T)) ⟶
      coefficient T (Arings l E T))
    (he : (c.scalar.ordinaryAdjunction.homEquiv _ _) e = scalarGenerator l E T) :
    (scalarSingleCounit c).app (coefficient T (Rrings l T)) ≫
        (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map e =
      c.scalarUnit.hom := by sorry
end AlgebraicGeometry.ProEtale.SpTowerClasses
