/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModel

/-! # Unit case of the finite scalar comparison formula

This isolates the unit middle coefficient case from the general pure-tensor
formula.  It is the normalized reassociation step in the finite coefficient
calculation.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, Step 4.
(blueprint: lem-weil-isomorphism-scalar-finite-comparison-formula-unit).
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

/-- The finite formula with the middle finite coefficient specialized to `1`.
Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, Step 4.
The normalized balanced reassociation sends the outer coefficient through the
finite inverse-image map and inserts the unit in the middle coefficient. -/
def FiniteFormulaUnit
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        (doublePure l E L ι g n P.obj i U s 1 x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) 1) x

/-- The unit case of the finite comparison is obtained from the completed
normalization by the canonical finite reassociation and coefficient transport.
The remaining proof is the unit calculation in the sheafified balanced tensor;
it uses the quotient-chain comparison and its normalized extension units.
(blueprint: lem-weil-isomorphism-scalar-finite-comparison-formula-unit).
-/
theorem finite_formula_unit_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n,
      FiniteFormulaUnit l E L ι g bfin := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
