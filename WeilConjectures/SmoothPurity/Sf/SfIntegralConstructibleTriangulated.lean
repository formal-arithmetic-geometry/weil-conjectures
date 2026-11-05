/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-!
# Triangulation of the intrinsic integral constructible category

Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the uniform-reduction
variant in blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).

The predicate is the recorded `sfIntegralConstructible`, over the completed coefficient
sheaf on the small pro-etale site. The two instances below make Mathlib's inherited
shift, pretriangulation, triangulation and exact full-subcategory inclusion available
on `sfIntegralConstructibleCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

end WeilConjectures
