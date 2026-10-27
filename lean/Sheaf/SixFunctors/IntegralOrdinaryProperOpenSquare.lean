/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction

/-! # Ordinary coefficient squares for proper/open interchange

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

/-- The ordinary coefficient square for the proper/open interchange.
Source: blueprint fix-prop-coherence, the canonical proper/open lambda adjunct.
(blueprint: lem-sf-integral-ordinary-proper-open-square).

Proof: expand gamma as the open adjunct of inverse lambda. The canonical bridge
identifies the system lambda with the cartesian open-base-change, clopen lift and
proper-composition factors. The ringed lambda has exactly the independent ringed
factors. Their coefficient squares follow from pull-composition, open base change,
clopen adjunction normalization and proper composition. Paste, invert the resulting
lambda square, and transpose under the actual open adjunction using its counit
square. Naturality inserts the coefficient map of e. The computation is in whole
systems and ordinary ringed categories; no completion or expression comparison is used. -/
theorem ordinaryProperOpenSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
    [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
    [hr : IsProper r.left] [hp : IsProper p.left]
    (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X U) :
    (Expression.shriek i hi qi (.push r hr e)).ordinaryReduction l E o a K ≫
      (a.properOpen.gamma k.left r.left p.left i.left w).app
        (e.systemObj l E o ((inputReduction l E X).obj K)) =
    (calculus l E Z.left).reduction.map
        ((a.ringedProperOpen.gamma k.left r.left p.left i.left w).app
          (e.ringedObj l E a.ringedModels K)) ≫
      (Expression.push p hp (.shriek k hk qk e)).ordinaryReduction l E o a K := by sorry


end WeilConjectures.IntegralSystemRealization
