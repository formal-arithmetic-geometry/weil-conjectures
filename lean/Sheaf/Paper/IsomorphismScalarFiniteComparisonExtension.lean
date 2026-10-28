/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit

/-! # Extension from the unit finite comparison formula

This is the scalar-linearity step extending the normalized unit calculation to
all middle finite coefficients.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, Step 4.
(blueprint: lem-weil-isomorphism-scalar-finite-comparison-formula-extension).
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

/-- Scalar linearity extends the unit calculation to every pure middle tensor.
The proof applies the balancing relation in the sheafified tensor and the
normalization of the finite scalar extension map.
(blueprint: lem-weil-isomorphism-scalar-finite-comparison-formula-extension). -/
theorem finite_formula_of_unit
    (bfin : ∀ n : ℕ,
      (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (hunit : FiniteFormulaUnit l E L ι g bfin) :
    FiniteFormula l E L ι g bfin := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
