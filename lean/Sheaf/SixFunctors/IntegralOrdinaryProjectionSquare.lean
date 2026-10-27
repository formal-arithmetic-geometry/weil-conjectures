/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction

/-! # Ordinary coefficient projection square

Source: blueprint fix-prop-coherence, the projection component of the normalized
mate argument for `lem-sf-integral-ordinary-exchange-projection-squares`.

The proof is split from the conjunction theorem so that the projection mate can
be proved independently by expanding the right-adjoint projection map and
pasting tensor, pullback, unit, and counit comparison squares. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Projection component of the ordinary coefficient mate square.
Source: Stacks Tags 07A7 and 0E48; blueprint fix-prop-coherence.
(blueprint: lem-sf-integral-ordinary-exchange-projection-squares).

Proof: expand the proper projection into its unit, tensor comparison, and
counit. Apply the ordinary tensor and pullback comparison equations, then paste
with the unit and counit identities of the proper adjunction. Naturality inserts
both expression coefficient maps. No cartesianness or invertibility is used.
-/
theorem ordinaryProjectionSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    ∀ {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) (t : Expression B I X V),
      (Expression.tensor (.push f hf e) t).ordinaryReduction l E o a K ≫
        ((properProjection l E o f.left).app
          (e.systemObj l E o ((inputReduction l E X).obj K))).app
            (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (((ringedProperProjection l E a.ringedModels f.left).app
            (e.ringedObj l E a.ringedModels K)).app (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.push f hf (.tensor e (.pull f t))).ordinaryReduction l E o a K := by
  sorry

end WeilConjectures.IntegralSystemRealization
