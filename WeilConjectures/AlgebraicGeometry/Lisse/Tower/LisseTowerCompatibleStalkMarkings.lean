/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerIsomorphismSections
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicRestrictedTower
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLisseTowerSectionCover

/-! # Compatible markings for a supplied algebraic stalk tower

Source: Stacks Project, proetale.tex, Tags 09BV and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso pbcDerivedRestrict constantAdicFiniteProjection

end AlgebraicGeometry.Scheme
