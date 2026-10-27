/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LisseLocalizationData

/-! # Exact localization data for completed integral coefficients

Source: Bhatt--Scholze 6.8.14(2); Stacks 015F, 010N and 06YY.
(blueprint: lem-tw-lisse-localization-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
open SheafOfModules WeilConjectures.LisseLocalizationInterfaces
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
namespace WeilConjectures.LisseLocalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact ordinary localization and its raw rational descent over one scheme.
Source: Bhatt--Scholze 6.8.14(2); Stacks 015F, 010N and 06YY
(blueprint: lem-tw-lisse-localization-existence).

Proof: take a universal cochain change-of-rings model for B → B[1/t]. Apply
rationalContinuousCoefficient_derivedLocalization to the compatible constant R-action.
The fraction-normalized algebra isomorphism with E is unique by localization, hence
is the recorded sfRationalCoefficientEquiv. Its exactness, normalized comparison and
cohomology isomorphisms give the first fields. Apply raw fraction descent to the full
integral constructible subcategory to obtain realization, its object equation and
pure-tensor map formula. For each rational half choose its defining integral
representative and rational isomorphism. The cohomology formula and additivity kill
all forbidden cohomology of that representative. Apply realization to the rational
isomorphism and transport this vanishing. This proves halves separately and requires
no common integral lattice. -/
theorem nonempty_localizationData (X : Scheme.{u}) :
    Nonempty (LocalizationData l E X) := by
  sorry

end WeilConjectures.LisseLocalization
