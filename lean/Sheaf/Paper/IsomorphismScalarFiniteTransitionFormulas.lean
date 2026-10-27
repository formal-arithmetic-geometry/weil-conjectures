/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModel

/-! # Finite scalar transition formulas

This is the adjacent-transition component of the finite scalar model.  It is
split from the finite comparison and quotient-map constructions.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-isomorphism-scalar-finite-transition-formulas).
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
The adjacent transition maps on the two finite scalar models exist and satisfy
their local formulas.

Proof source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, Step 6.
Use the quotient transition on each coefficient factor and the compatibility
of the scalar quotient map with those transitions.  Lift the resulting maps
termwise to complexes and use the sheafified tensor universal property to
obtain the displayed formulas on pure tensors.  This construction is
independent of the finite comparison and quotient maps.
(blueprint: lem-weil-isomorphism-scalar-finite-transition-formulas).
-/
theorem transition_formulas_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n,
      LeftTransitionFormula l E L ι g tleft ∧
    ∃ tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n,
      RightTransitionFormula l E L ι g tright := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
