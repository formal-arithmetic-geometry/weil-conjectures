/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConnectedEtalePresentation
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # Separate local markings of the algebraic stalk tower

Source: Stacks Project, proetale.tex, Tags 09BV and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

-- Preserve the original proof-binder names in the statement.

end AlgebraicGeometry.Scheme
