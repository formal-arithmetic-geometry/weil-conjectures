/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantStalkModels

/-! # Local algebraic diagrams over the constant completion ring

Source: Stacks Tag 09BV, finite-ring derived local constancy and compatible
trivializations in amplification (c).
(blueprint: lem-weil-pbc-lisse-tower-constant-algebraic-reduction-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] constantAdicFiniteRealization

-- Keep the published name of the compatibility binder, unused in its conclusion.

end AlgebraicGeometry.Scheme
