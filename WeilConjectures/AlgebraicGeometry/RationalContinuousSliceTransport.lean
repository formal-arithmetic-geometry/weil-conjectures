/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRationalRealizationData

import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientSliceNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # The normalized rational restriction to a pro-etale slice

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL and 00XZ
(blueprint: lem-per-rational-continuous-slice-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational

/-- Express the exact slice comparison in the published rational coefficient presentation.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL and 00XZ
(blueprint: lem-per-rational-continuous-slice-transport).

Proof: take the actual weakly-etale slice equivalence and its continuous structure.
Its composite with the forgetful functor is siteInclude. On continuous functions the
restricted rational ring and the rational ring of U have the same sections and
restriction functions; the identity functions give ring, including its normalization.
Use the continuous-coefficient slice normalization theorem for its Adic rational
isomorphism and module comparison. Remove the inserted identity tensor factor by
multiplication and identify literal module restriction with overFunctor followed by
pushforward along the slice equivalence and the identity-on-sections ring isomorphism.
The module adjunction unit formula is restriction along the actual pullback projection;
this is comparison_units. The literal restriction is exact, so the ordinary pullback
is additive and preserves finite limits and colimits. Its mapDerivedCategory is a
left derived functor with its computation isomorphism. The general derived tensor
counit, after removing the identity factor termwise, has the same universal property;
uniqueness of left derived functors gives the displayed derived isomorphism normalized
by their counits. No noetherian or dimension hypothesis is imposed on U.left. -/
theorem rationalContinuousSliceTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEt) : Nonempty (SiteRestriction l E X U) := by
  sorry

end AlgebraicGeometry.Scheme.ContinuousRational
