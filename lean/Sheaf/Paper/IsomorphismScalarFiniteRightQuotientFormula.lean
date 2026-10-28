/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModel

/-! # Right finite scalar quotient formula

This is the right half of the finite quotient construction.  It is separated
from the left map because its unit insertion is formed before inverse image and
therefore has an independent pure-tensor calculation.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-isomorphism-scalar-finite-right-quotient-formula)
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

/-- The right completed-to-finite quotient map and its pure-tensor formula.

The map is obtained from the scalar-extension unit followed by the finite
projection on the target and transported through inverse image.  The concrete
presentation transport is the right component of the quotient-chain
calculation and is isolated as this strictly smaller obligation.
-/
theorem right_quotient_formula_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n,
      RightQuotientFormula l E L ι g vright := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
