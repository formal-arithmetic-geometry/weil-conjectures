/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralScalarExtensionWellDefined

/-! # Canonical completed integral scalar data

Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.14(1); Stacks Tag 03EK
(blueprint: def-weil-completed-integral-scalar-data).

The constructions of this definition node are the published ones, reexported here:
`completedCoefficientMap` (the unique completed map with the prescribed finite residues),
`completedScalarChangeData`, `completedOrdinaryScalarExtension`,
`completedScalarTensorSection` and `completedScalarRelativeDegree` from
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`, and `integralScalarIntegerInclusion`,
`integralScalarFiniteConstant` and `integralScalarConstant` from
`Sheaf.Paper.IntegralScalarExtensionWellDefined`. No construction is redeclared.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe t u
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The completed coefficient inclusion c : R_E → R_L of this definition node: a
transparent name for the published `completedCoefficientMap`, the unique map whose
composite with every finite projection is the quotient inclusion.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: def-weil-completed-integral-scalar-data). -/
abbrev completedIntegralScalarCoefficientMap :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
  completedCoefficientMap l E L ι Y

end WeilConjectures
