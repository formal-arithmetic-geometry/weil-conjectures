/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.Topology.Category.TopCat.Basic
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientPullback

/-! # Canonical pullback of continuous coefficient sections

Source: Bhatt--Scholze, Definition 6.8.1 and the paragraph before Definition 6.8.6.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
