/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q8
-/
module

public import Sheaf.Paper.IsomorphismScalarFiniteCore

/-! # Commutative squares for the finite scalar model

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-isomorphism-scalar-finite-model-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/--
The finite quotient and transition maps from the finite formula construction
satisfy the two naturality squares. The hypotheses are exactly the five local
formula predicates; tensor generation and naturality identify the corresponding
natural transformations. This is strictly the square part of the finite model.

Proof source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, Steps 5--6.
Both squares are checked on pure tensors: the quotient square inserts the unit
and the transition square reduces the two scalar factors. The argument includes
ramified extensions and does not use surjectivity or flatness.
(blueprint: lem-weil-isomorphism-scalar-finite-model-squares).
-/
theorem scalar_finite_squares
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (hF : FiniteFormula l E L ι g bfin)
    (hL : LeftQuotientFormula l E L ι g vleft)
    (hR : RightQuotientFormula l E L ι g vright)
    (hTL : LeftTransitionFormula l E L ι g tleft)
    (hTR : RightTransitionFormula l E L ι g tright) :
    QuotientSquare l E L ι g b bfin vleft vright ∧
    TransitionSquare l E L ι g bfin tleft tright := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
