/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantAlgebraicReductionDiagram
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantUnboundedFiniteDiagramComparison

/-! # Local finite algebra diagrams for lisse towers

Source: Stacks Project, proetale.tex, Tag 09BV, and the bounded-derived
local-constancy argument in amplification (c).
(blueprint: lem-weil-pbc-lisse-tower-local-algebraic-reduction-diagram).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Preserve the original names of proof binders inside the theorem statement.

end AlgebraicGeometry.Scheme
