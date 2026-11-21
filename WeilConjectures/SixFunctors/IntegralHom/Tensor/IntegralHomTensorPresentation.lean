/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterEvaluation

/-! # Existence of the normalized integral tensor model

This is the tensor and evaluation part of the existence of normalized integral
tensor-Hom models.

## References

* [Stacks, Tag 06YS]
* [Stacks, Tag 06YU]
* [Stacks, Tag 08J9]
* [Stacks, Tag 08JA]
* [Stacks, Tag 07A4]
* [Stacks, Tag 07A6]
* [Stacks, Tag 0A8X]
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- A normalized tensor presentation exists. -/
theorem tensor_presentation_exists :
    Nonempty (TensorPresentation.{t, u} Y
        (completedIntegralCommRingSheaf l E Y D hl)) := by
  classical
  letI : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  letI : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  letI : HasDerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) := HasDerivedCategory.standard _
  obtain ⟨S, T, _, _⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
      (max u (t + 1)) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl)
  obtain ⟨adj, hev⟩ := tensor_presentation_parameter_evaluation l E Y D hl S T
  exact ⟨TensorPresentation.mk S.tensor T.comparison adj hev⟩

end WeilConjectures.IntegralHom
