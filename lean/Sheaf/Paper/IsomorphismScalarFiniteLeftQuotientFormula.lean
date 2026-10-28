/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModel

/-! # Left finite scalar quotient formula

This is the left half of the finite quotient construction.  It is separated from
its right counterpart because the two maps use different adjunction units and are
checked independently on pure tensors.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-isomorphism-scalar-finite-left-quotient-formula)
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

/-- The left completed-to-finite quotient map and its pure-tensor formula.

The map is obtained by inserting the unit for the completed scalar extension,
then applying the finite projection.  The remaining work is the concrete
transport from the canonical scalar-extension presentation to the selected
`finiteChangeData`; this is exactly the left component of the quotient-chain
calculation and is intentionally isolated here.
-/
theorem left_quotient_formula_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n,
      LeftQuotientFormula l E L ι g vleft := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
