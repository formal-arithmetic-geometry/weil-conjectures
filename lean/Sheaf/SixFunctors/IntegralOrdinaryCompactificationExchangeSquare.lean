/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction
import Sheaf.SixFunctors.OrdinaryBasicSquare

/-! # Ordinary coefficient compatibility for compactification exchange

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
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

/-- Ordinary coefficient compatibility with the fixed compactification exchange.
Source: blueprint fix-prop-coherence, the prescribed proper/open exchange composite.
(blueprint: lem-sf-integral-ordinary-compactification-exchange-square).

Proof: the prescribed compactification exchange and its ringed counterpart are
exactly the arrows of BasicPair.compactExchange. Specialize the existing ordinary
coefficient square for a basic pair to that constructor, with the given ordinary
inputs. The constructor retains both specified composites and all the given
compactification data; no map or hypothesis is replaced.
-/
theorem ordinaryCompactificationExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K := by
  exact ordinaryBasicSquare l E o a K
    (BasicPair.compactExchange f f' cf cf' x y z wi wp hi e)

end WeilConjectures.IntegralSystemRealization
