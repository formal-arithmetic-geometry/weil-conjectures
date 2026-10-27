/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction

/-! # Ordinary coefficient squares for compactification composites

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

/-- Ordinary coefficient squares for the fixed open/proper compactification words.
Source: blueprint fix-prop-coherence, expansion of compactification exchange and projection.
(blueprint: lem-sf-integral-ordinary-compactification-squares).

Proof: expand compactificationExchangeFromData: proper exchange on the open image,
then proper image of open base change. Obtain the proper-exchange coefficient
square by applying the primitive square to formal variables for the open-image
objects and inserting the actual open coefficient by naturality. For the open
base-change factor, transpose its defining open-adjunction equation. Pullback
composition coherence and the unit/counit mate squares identify its reduction;
invertibility of the fixed openReduction permits cancellation. This direct mate
argument needs no quasi-compactness of the compactification open. Whisker by
proper image using ordinaryPushReduction.naturality, and paste the two squares.
For projection, expand its three factors: proper projection, proper image of open
projection, and open/proper image of the inverse pull compositor with cf.comm.
The proper-projection square at formal variables extends to the open-image
coefficient and the other child coefficient by naturality in both inputs. The
open projection square follows by transposing its prescribed inverse: tensor
reduction compatibility and the open unit square identify the two transposes,
and openReduction is invertible. Apply inverse pull-composition compatibility
to the last factor and transport by cf.comm. Bifunctoriality pastes these three
squares and inserts both child coefficients. No completion comparison is used. -/
theorem ordinaryCompactificationSquares
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    (∀ {U V U' V' : Over B}
      (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
      (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U),
      (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K) ∧
    (∀ {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (e : Expression B I X U) (t : Expression B I X V),
      (Expression.tensor (.compactSupport f cf e) t).ordinaryReduction l E o a K ≫
        compactificationProjection l E o a.compositors a.openComparisons cf
          (e.systemObj l E o ((inputReduction l E X).obj K))
          (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (ringedCompactificationProjection l E a.ringedModels a.ringedOpenComparisons cf
            (e.ringedObj l E a.ringedModels K)
            (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f cf (.tensor e (.pull f t))).ordinaryReduction
          l E o a K) := by sorry


end WeilConjectures.IntegralSystemRealization
