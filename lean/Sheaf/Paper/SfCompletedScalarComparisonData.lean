/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.CompletedIntegralScalarData

/-! # Canonical completed scalar comparison data

Source: Bhatt--Scholze, Lemma 6.8.2(1) and Proposition 3.5.1
(blueprint: def-sf-completed-scalar-comparison-data).

The coefficient map is the residue-normalized `completedIntegralScalarCoefficientMap`
owned by `def-weil-completed-integral-scalar-data`, publicly reexported here.
The ordinary and derived extensions, K-flat counit, strict quotient-Roos chain map,
and its unique derived descent are the published constructions of
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`. This module supplies a transparent
name for that descent; it makes no new choice and asserts no invertibility theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe t u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The canonical comparison from ordinary derived scalar extension to completed extension.
It is the existing unique descent of the strict quotient-Roos chain comparison, fixed
on good representatives by the universal K-flat computation counit. In particular this
is a transparent name for the published construction, with no additional existence choice.
Source: Bhatt--Scholze, Lemma 6.8.2(1) and Proposition 3.5.1
(blueprint: def-sf-completed-scalar-comparison-data). -/
abbrev completedIntegralScalarComparison :
    completedDerivedScalarExtension l E L ι Y ⟶ integralScalarExtensionOfUniverses l E L ι Y :=
  completedScalarComparison l E L ι Y

end WeilConjectures
