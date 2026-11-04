/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcScalarCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence

/-! # The finite-free inverse scalar mate for the completed coefficient inclusion

The completed target coefficient sheaf is finite free over the completed source coefficient
sheaf, so the inverse scalar mate of the canonical restriction/direct-image comparison is
invertible.

Source: Stacks Project, Tags 0B56 and 07A6; Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

/-- The completed target coefficient sheaf is finite free over the completed source one.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcScalarCoefficientMap_finiteFree (W : Scheme.{u}) :
    ∃ d : ℕ, Nonempty
      ((pbcRestrict (pbcScalarCoefficientMap l E F i W)).obj
          (SheafOfModules.unit ((adicLisseForget W).obj
            (pbcAdicCompletion W (pbcIntegralDatum l F)))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj
          (pbcAdicCompletion W (pbcIntegralDatum l E)))) := by
  sorry

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The inverse scalar mate of the canonical restriction/direct-image comparison is
invertible for the completed coefficient inclusion.
Source: Stacks Project, Tags 0B56 and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcScalarRestrictionDirectImageMate_isIso :
    IsIso (((mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedDirectImage g
          (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
          (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
          (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
          (pbcActualCoefficientIso g _) (pbcActualCoefficientIso g _)
          (pbcScalarCoefficientMap_inverseImage l E F i g)).inv)).natTrans) := by
  sorry

end AlgebraicGeometry.Scheme
