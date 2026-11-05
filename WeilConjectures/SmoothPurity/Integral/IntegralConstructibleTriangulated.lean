/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-!
# Integral constructible complexes form a triangulated subcategory

Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the uniform-reduction
variant in blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory

namespace WeilConjectures

end WeilConjectures

/- Stage-2 paired-interface rebuild for NZ integral Tor triangulation. -/
