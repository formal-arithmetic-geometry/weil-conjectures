/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction

/-! # Ordinary coefficient square for a basic pair

This isolates the generic basic-pair square needed by the exchange component.
Source: blueprint `lem-sf-integral-basic-generator-square`.
(blueprint: lem-sf-integral-ordinary-basic-square).
-/

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

/-- The ordinary coefficient square attached to any basic pair.

Source: blueprint `lem-sf-integral-basic-generator-square`; the square is obtained
by transposing the ordinary reduction map through the reduction/limit adjunction,
then treating the canonical, unit/counit, exchange, projection, proper/open and
compactification constructors separately. Each constructor uses its normalized
mate equation and the recursive coefficient map. The proof is independent of any
finite evaluation and works for the full basic-pair inductive family.
(blueprint: lem-sf-integral-ordinary-basic-square).
-/
theorem ordinaryBasicSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)}
    {r : e.ringedObj l E a.ringedModels K ⟶
      t.ringedObj l E a.ringedModels K}
    (h : BasicPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K) K e t s r) :
    e.ordinaryReduction l E o a K ≫ s =
      (calculus l E W.left).reduction.map r ≫ t.ordinaryReduction l E o a K := by
  sorry

end WeilConjectures.IntegralSystemRealization
