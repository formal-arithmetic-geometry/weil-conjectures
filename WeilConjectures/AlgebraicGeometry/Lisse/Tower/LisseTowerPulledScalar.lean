/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction

/-! # The coefficient square after a further fixed-coefficient inverse image

Source: Stacks Project, Tags 03CY, 03DA and 06YY. The square is built from the
section-normalized ordinary coefficient square, the exact inverse-image coefficient
mate, and the specified restriction-of-scalars compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicFiniteProjection

end AlgebraicGeometry.Scheme
